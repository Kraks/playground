module L = List

module CEKMachine = struct
  type var = string

  type term = 
    | Var of var
    | Lam of string * term
    | App of term * term

  let rec string_of_term = function
    | Var x -> x
    | Lam (x, t) -> "(λ" ^ x ^ "." ^ (string_of_term t) ^ ")"
    | App (t1, t2) -> "(" ^ (string_of_term t1) ^ " " ^ (string_of_term t2) ^ ")"
  
  type control = term

  type mvalue =
    | Clo of term * env
  and env = 
    (var * mvalue) list
  and cont =
    | Done
    | EvalArg of term * env * cont
    | Call    of term * env * cont

  let extend var value env = (var, value)::env
  
  exception FreeVariable of string

  let rec lookup var = function
    | [] -> raise (FreeVariable var)
    | (k, (v:mvalue))::env -> if (k = var) then v else lookup var env

  type machine = control * env * cont

  let rec string_of_env env =
    (L.fold_left (fun acc (k, v) -> acc ^ k ^ "|->" ^ (string_of_mvalue v)) "[" env) ^ "]"
  and string_of_mvalue = function
    | Clo (t, env) -> "{" ^ (string_of_term t) ^ "w/ env " ^ (string_of_env env) ^ "}"

  let rec string_of_cont = function
    | Done -> "[]"
    | EvalArg (t, e, k) -> "Arg[" ^ (string_of_term t) ^ "," ^ (string_of_env e) ^ "," ^ (string_of_cont k) ^ "]"
    | Call (t, e, k) -> "Call[" ^ (string_of_term t) ^ "," ^ (string_of_env e) ^ "," ^ (string_of_cont k) ^ "]"

  let string_of_machine(c, e, k) = "<" ^ (string_of_term c) ^ ", " 
                                    ^ (string_of_env e) ^ ", "
                                    ^ (string_of_cont k) ^ ">"

  let step state = match state with
    | (Var x, e, k) -> (match (lookup x e) with
                        | Clo(lambda, e') -> (lambda, e', k))
    | (App (t1, t2), e, k) -> (t1, e, EvalArg(t2, e, k))
    | (Lam (x, t), e, EvalArg(t', e', k)) ->
        (t', e', Call(Lam(x, t), e, k))
    | (Lam (x, t), e, Call(Lam(x', t'), e', k)) ->
        let ext_env = extend x' (Clo(Lam (x, t), e)) e' in
          (t', ext_env, k)
    | (_, _, Done) -> state
    | _ -> failwith "no step defined"

  let inject t = (t, [], Done)

  let run t = 
    let rec aux state = 
      print_bytes ((string_of_machine state) ^ "\n");
      match step state with
        | (Lam _, _, Done) as state' -> print_bytes ((string_of_machine state') ^ "\n"); print_bytes "Done\n"
        | state' -> aux state'
    in aux (inject t)

end

open CEKMachine

let example = App(Lam("x",Var "x"), Lam("y",Var "y"));;

run example
