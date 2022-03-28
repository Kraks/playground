datatype exp = LIT of int
             | VAR of string
             | LAM of string * exp
             | APP of exp * exp
             | ADD of exp * exp;

datatype univ = INT of int
              | FUN of univ -> univ;

signature ENV = sig
  type 'a env
  val empty : 'a env
  val extend : string * 'a * 'a env -> 'a env
  val lookup : string * 'a env -> 'a
end;

structure Env : ENV = struct
  type 'a env = (string * 'a) list
  val empty = nil
  fun extend (x, v, env) = (x, v)::env
  fun lookup (x, []) = raise Empty
    | lookup (x, (x', v)::xs) = if x = x' then v else lookup (x, xs)
end;

exception TYPE_ERROR;

(* app : univ * univ -> univ *)
fun app (FUN f, v) = f v
  | app _ = raise TYPE_ERROR;

(* add : univ * univ -> univ *)
fun add (INT i1, INT i2) = INT (i1 + i2)
  | add _ = raise TYPE_ERROR;

(* eval : exp -> univ Env.env -> univ *)
fun eval (LIT i) env = INT i
  | eval (VAR x) env = Env.lookup (x, env)
  | eval (LAM (x, e)) env = FUN (fn v => eval e (Env.extend (x, v, env)))
  | eval (APP (e0, e1)) env = app (eval e0 env, eval e1 env)
  | eval (ADD (e0, e1)) env = add (eval e0 env, eval e1 env);
