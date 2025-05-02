(* Interderivation of type checkings *)

datatype term = Lit of int
	      | Ide of string
	      | Lam of string * typ * term
	      | App of term * term
     and typ = TNum
	     | TArr of typ * typ
	     | TErr of string

signature TENV =
sig
  type 'a gamma
  val empty : (string * 'a) gamma
  val extend : string * 'a * (string * 'a) gamma -> (string * 'a) gamma
  val lookup : string * (string * 'a) gamma -> 'a option
end

exception Typing_error of string

structure TEnv : TENV =
struct
  type 'a gamma = 'a list
  val empty = []
  fun extend (x, v, env) = (x, v) :: env
  fun lookup (x, []) = raise (Typing_error "undefined variable")
    | lookup (x, (x', v)::env) = if x = x' then (SOME v) else lookup (x, env)
end

fun check0 (Lit n, gamma) = TNum
  | check0 (Ide x, gamma) = (case TEnv.lookup (x, gamma) of (SOME t) => t)
  | check0 (Lam (x, arg_t, body), gamma) =
    let val body_t = check0 (body, TEnv.extend (x, arg_t, gamma)) in
      TArr (arg_t, body_t)
    end
  | check0 (App (e1, e2), gamma) =
    let val TArr (t1, t2) = check0 (e1, gamma)
	val e2_t = check0 (e2, gamma)
    in if t1 = e2_t then t2 else raise (Typing_error "type mismatch")
    end

fun type_check0 t = check0 (t, TEnv.empty)

fun check1 (Lit n, s, e) = TNum :: s
  | check1 (Ide x, s, e) = (case TEnv.lookup (x, e) of (SOME t) => t :: s)
  | check1 (Lam (x, arg_t, body), s, e) =
    let val (body_t :: _) = check1 (body, [], (TEnv.extend (x, arg_t, e)))
    in TArr (arg_t, body_t) :: s
    end
  | check1 (App (e1, e2), s, e) =
    let val s0 as (TArr (t1, t2) :: _) = check1 (e1, [], e)
	val (arg_t :: _) = check1 (e2, s0, e)
    in if arg_t = t1 then t2 :: s
       else raise (Typing_error "type mismatch")
    end

