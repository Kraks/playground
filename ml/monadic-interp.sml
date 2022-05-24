(* Reference:
 * A functional correspondence between monadic evaluators and abstract machines
 * for languages with computational effects *)

(* A call-by-value monadic evaluator *)
datatype term = LIT of int
              | VAR of string
              | LAM of string * term
              | APP of term * term
              | HANDLE of term * term

signature MONAD =
sig
  type 'a monad
  val return : 'a -> 'a monad
  val bind : 'a monad * ('a -> 'b monad) -> 'b monad
end

(* Left unit: bind (return a, k) = k a
 * Right unitL bind (m, return) = m
 * Associativity: bind (m, fn a => bind (k a, h)) = bind (bind (m, k), h)
 *
 *)

signature ENV =
sig
  type 'a env
  val empty : 'a env
  val extend : string * 'a * 'a env -> 'a env
  val lookup : string * 'a env -> 'a
end

structure Env : ENV =
struct
  type 'a env = (string * 'a) list
  val empty = nil
  fun extend (x, v, env) = (x, v)::env
  fun lookup (x, []) = raise Empty
    | lookup (x, (x', v)::xs) = if x = x' then v else lookup (x, xs) 
end

functor Value (structure M : MONAD) = 
struct
  datatype value = NUM of int
                 | FUN of value -> value M.monad
end

functor Interp (structure Env : ENV; structure M : MONAD) =
struct
  structure ValueM = Value (structure M = M)
  open ValueM

  fun eval (LIT i, e) = M.return (NUM i)
    | eval (VAR x, e) = M.return (Env.lookup (x, e))
    | eval (LAM (x, t), e) =
      M.return (FUN (fn v => eval (t, Env.extend (x, v, e))))
    | eval (APP (t0, t1), e) =
      M.bind (eval (t0, e),
              fn v0 => M.bind (eval (t1, e),
                               fn v1 => let val (FUN f) = v0
                                        in f v1 end))

  val env0 = Env.extend ("succ", FUN (fn (NUM i) => M.return (NUM (i+1))),
                         Env.empty)

  fun interp t = eval (t, env0)
end

(* Identity monad *)

structure Identity_Monad : MONAD =
struct
  type 'a monad = 'a
  fun return a = a
  fun bind (m, k) = k m
end

structure ideval = Interp (structure Env = Env
                           structure M = Identity_Monad)

val term1 = APP (VAR "succ", LIT 3)

(* State Monad *)

signature STATE_MONAD =
sig
  include MONAD
  type storable
  type state
  val get : storable monad
  val set : storable -> storable monad
end

structure State_Monad : STATE_MONAD =
struct
  type storable = int
  type state = storable
  type 'a monad = state -> 'a * state

  fun return a = fn s => (a, s)
  fun bind (m, k) = 
    fn s => let val (a, s') = m s
            in k a s' end

  val get = fn s => (s, s)

  fun set i = fn s => (s, i)
end

(* Exception Monad *)

signature EXCEPTION_MONAD =
sig
  include MONAD
  datatype 'a E = RES of 'a | EXC
  val raise_exception : 'a monad
  val handle_exception : 'a monad * (unit -> 'a monad) -> 'a monad
end

structure Exception_Monad : EXCEPTION_MONAD = 
struct 
  datatype 'a E = RES of 'a | EXC
  type 'a monad = 'a E

  fun return a = RES a
  fun bind (RES a, k) = k a
    | bind (EXC, k) = EXC
  val raise_exception = EXC
  fun handle_exception (RES a, h) = RES a
    | handle_exception (EXC, h) = h ()
end
