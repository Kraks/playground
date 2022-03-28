open Runcode;;
(* open Print_code;; *)

type exp = Int of int
         | Var of string
         | App of string * exp
         | Add of exp * exp
         | Sub of exp * exp
         | Mul of exp * exp
         | Div of exp * exp
         | If0 of exp * exp * exp
;;

type def = Declaration of string * string * exp;;

type prog = Program of def list * exp;;

exception Yikes;;

let mt_env = fun x -> raise Yikes;;
let mt_fenv = mt_env;;

let ext env x v = fun y -> if x = y then v else env y;;

(* eval1: exp -> (string -> int) -> (string -> int -> int) -> int *)
let rec eval1 e env fenv =
  match e with
    Int i -> i
  | Var s -> env s
  | App (s, e2) -> (fenv s)(eval1 e2 env fenv)
  | Add (e1, e2) -> (eval1 e1 env fenv) + (eval1 e2 env fenv)
  | Sub (e1, e2) -> (eval1 e1 env fenv) - (eval1 e2 env fenv)
  | Mul (e1, e2) -> (eval1 e1 env fenv) * (eval1 e2 env fenv)
  | Div (e1, e2) -> (eval1 e1 env fenv) / (eval1 e2 env fenv)
  | If0 (e1, e2, e3) -> if (eval1 e1 env fenv) = 0
                          then (eval1 e2 env fenv)
                          else (eval1 e3 env fenv)
;;

(* peval1: prog -> (string -> int) -> (string -> int -> int) -> int *)
let rec peval1 p env fenv =
  match p with
    Program ([], e) -> eval1 e env fenv
  | Program (Declaration (s1, s2, e1)::tl, e) ->
    let rec f x = eval1 e1 (ext env s2 x) (ext fenv s1 f)
    in peval1 (Program(tl, e)) env (ext fenv s1 f)
;;

let fact10 = Program ([Declaration
                         ("fact", "x", If0(Var "x",
                                           Int 1,
                                           Mul(Var "x",
                                               (App ("fact", Sub(Var "x", Int 1))))))],
                      App ("fact", Int 10))
;;

(* Staged version *)
(* eval2 : exp -> (string -> int code) -> (string -> (int -> int) code) -> int code *)
let rec eval2 e env fenv =
  match e with
    Int i -> .<i>.
  | Var s -> env s
  | App (s, e2) -> .<.~(fenv s).~(eval2 e2 env fenv)>.
  | Add (e1, e2) -> .<.~(eval2 e1 env fenv) + .~(eval2 e2 env fenv)>.
  | Sub (e1, e2) -> .<.~(eval2 e1 env fenv) - .~(eval2 e2 env fenv)>.
  | Mul (e1, e2) -> .<.~(eval2 e1 env fenv) * .~(eval2 e2 env fenv)>.
  | Div (e1, e2) -> .<.~(eval2 e1 env fenv) / .~(eval2 e2 env fenv)>.
  | If0 (e1, e2, e3) -> .<if .~(eval2 e1 env fenv)=0
                            then .~(eval2 e2 env fenv)
                            else .~(eval2 e3 env fenv)>.
;;

let rec peval2 p env fenv =
  match p with
    Program ([], e) -> eval2 e env fenv
  | Program (Declaration (s1, s2, e1)::tl, e) ->
    .<let rec f x = .~(eval2 e1 (ext env s2 .<x>.)
                                (ext fenv s1 .<f>.))
    in .~(peval2 (Program(tl, e)) env (ext fenv s1 .<f>.))>.
;;

(* Error handling *)

(* eval3 : exp -> (string -> int) -> (string -> int -> int option) -> int option *)
let rec eval3 e env fenv =
  match e with
    Int i -> Some i
  | Var s -> Some (env s)
  | App (s, e2) ->
    (match (eval3 e2 env fenv) with
       Some x -> (fenv s) x
     | None -> None)
  | Add (e1, e2) ->
    (match (eval3 e2 env fenv, eval3 e2 env fenv) with
       (Some x, Some y) -> Some (x + y)
     | _ -> None)
  | Sub (e1, e2) ->
    (match (eval3 e2 env fenv, eval3 e2 env fenv) with
       (Some x, Some y) -> Some (x - y)
     | _ -> None)
  | Mul (e1, e2) ->
    (match (eval3 e2 env fenv, eval3 e2 env fenv) with
       (Some x, Some y) -> Some (x * y)
     | _ -> None)
  | Div (e1, e2) ->
    (match (eval3 e2 env fenv, eval3 e2 env fenv) with
       (Some x, Some y) -> if y = 0 then None else Some (x / y)
     | _ -> None)
  | If0 (e1, e2, e3) ->
    (match (eval3 e1 env fenv) with
       Some x -> if x = 0 then (eval3 e2 env fenv)
                          else (eval3 e3 env fenv)
     | None -> None)
;;

(* eval4 : exp -> (string -> int code)
               -> (string -> (int -> int option) code)
               -> (int option) code *)
let rec eval4 e env fenv =
  match e with
    Int i -> .<Some i>.
  | Var s -> .<Some .~(env s)>.
  | App (s, e2) ->
    .<(match .~(eval4 e2 env fenv) with
          Some x -> .~(fenv s) x
        | None -> None)>.
  | Add (e1, e2) ->
    .<(match (.~(eval4 e2 env fenv), .~(eval4 e2 env fenv)) with
          (Some x, Some y) -> Some (x + y)
        | _ -> None)>.
  | Sub (e1, e2) ->
    .<(match (.~(eval4 e2 env fenv), .~(eval4 e2 env fenv)) with
          (Some x, Some y) -> Some (x - y)
        | _ -> None)>.
  | Mul (e1, e2) ->
    .<(match (.~(eval4 e2 env fenv), .~(eval4 e2 env fenv)) with
          (Some x, Some y) -> Some (x * y)
        | _ -> None)>.
  | Div (e1, e2) ->
    .<(match (.~(eval4 e2 env fenv), .~(eval4 e2 env fenv)) with
          (Some x, Some y) -> if y = 0 then None else Some (x / y)
        | _ -> None)>.
  | If0 (e1, e2, e3) ->
    .<(match .~(eval4 e1 env fenv) with
          Some x -> if x = 0 then .~(eval4 e2 env fenv)
                             else .~(eval4 e3 env fenv)
        | None -> None)>.
;;

(* CPS Interpreter *)
(* eval5 : exp -> (string -> int) -> (string -> int -> int)
               -> (int option -> 'a) -> 'a *)
(* let rec eval5 e env fenv k = *)
let rec eval5 e env fenv k =
  match e with
    Int i -> k (Some i)
  | Var s -> k (Some (env s))
  | App (s, e2) -> eval5 e2 env fenv
                     (fun r -> match r with
                          Some x -> k (Some ((fenv s) x))
                        | None -> k None)
  | Add (e1, e2) -> eval5 e1 env fenv
                      (fun r -> eval5 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> k (Some (x + y))
                             | _ -> k None))
  | Sub (e1, e2) -> eval5 e1 env fenv
                      (fun r -> eval5 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> k (Some (x - y))
                             | _ -> k None))
  | Mul (e1, e2) -> eval5 e1 env fenv
                      (fun r -> eval5 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> k (Some (x * y))
                             | _ -> k None))
  | Div (e1, e2) -> eval5 e1 env fenv
                      (fun r -> eval5 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> if y = 0 then k None
                                                            else k (Some (x / y))
                             | _ -> k None))
  | If0 (e1, e2, e3) -> eval5 e1 env fenv
                          (fun r -> match r with
                               Some z -> if z = 0 then (eval5 e2 env fenv k)
                               else (eval5 e3 env fenv k)
                             | None -> k None)
;;

let rec pevalK5 p env fenv k =
  match p with
    Program ([], e) -> eval5 e env fenv k
  | Program (Declaration (s1, s2, e1)::tl, e) ->
    let rec f x = eval5 e1 (ext env s2 x) (ext fenv s1 f) k
    in pevalK5 (Program(tl, e)) env (ext fenv s1 f) k
;;

let peval5 p env fenv =
  pevalK5 p env fenv (function Some x -> x
                             | None -> raise Division_by_zero)
;;

(* Staged CPS Interpreter *)
(* eval6 : exp -> (string -> int code) -> (string -> (int -> int) code)
               -> (int code option -> 'b code) -> 'b code *)

let rec eval6 e env fenv k =
  match e with
    Int i -> k (Some .<i>.)
  | Var s -> k (Some (env s))
  | App (s, e2) -> eval6 e2 env fenv
                     (fun r -> match r with
                          Some x -> k (Some .<.~(fenv s) .~x>.)
                        | None   -> k None)
  | Add (e1, e2) -> eval6 e1 env fenv
                      (fun r -> eval6 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> k (Some .<.~x + .~y>.)
                             | _ -> k None))
  | Sub (e1, e2) -> eval6 e1 env fenv
                      (fun r -> eval6 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> k (Some .<.~x - .~y>.)
                             | _ -> k None))
  | Mul (e1, e2) -> eval6 e1 env fenv
                      (fun r -> eval6 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> k (Some .<.~x * .~y>.)
                             | _ -> k None))
  | Div (e1, e2) -> eval6 e1 env fenv
                      (fun r -> eval6 e2 env fenv
                          (fun s -> match (r, s) with
                               (Some x, Some y) -> .<if .~y=0 then .~(k None)
                                                              else .~(k (Some .<.~x / .~y>.))>.
                             | _ -> k None))
  | If0 (e1, e2, e3) -> eval6 e1 env fenv
                          (fun r -> match r with
                               Some x -> .<if .~x=0 then .~(eval6 e2 env fenv k)
                                                    else .~(eval6 e3 env fenv k)>.
                             | None -> k None)
;;

let rec pevalK6 p env fenv k =
  match p with
    Program ([], e) -> eval6 e env fenv k
  | Program (Declaration (s1, s2, e1)::tl, e) ->
    .<let rec f x = .~(eval6 e1 (ext env s2 .<x>.) (ext fenv s1 .<f>.) k)
    in .~(pevalK6 (Program(tl, e)) env (ext fenv s1 .<f>.) k)>.
;;

let peval6 p env fenv =
  pevalK6 p env fenv (function Some x -> x
                             | None -> .<raise Division_by_zero>.)
;;

Format.printf "peval1: %d\n" (peval1 fact10 mt_env mt_fenv);;

print_code Format.std_formatter (peval2 fact10 mt_env mt_fenv);;
Format.printf "peval2: %d\n" (run (peval2 fact10 mt_env mt_fenv));;

Format.printf "peval5: %d\n" (peval5 fact10 mt_env mt_fenv);;

print_code Format.std_formatter (peval6 fact10 mt_env mt_fenv);;
Format.printf "peval6: %d\n" (run (peval6 fact10 mt_env mt_fenv));;

