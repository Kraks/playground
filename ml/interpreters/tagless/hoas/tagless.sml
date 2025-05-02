datatype exp = LIT of int
             | LAM of exp -> exp
             | APP of exp * exp
             | ADD of exp * exp

datatype univ = INT of int
              | FUN of univ -> univ

exception TYPE_ERROR;
exception NOT_A_VALUE;

(* app : univ * univ -> univ *)
fun app (FUN f, v) = f v
  | app _ = raise TYPE_ERROR;

(* add : univ * univ -> univ *)
fun add (INT i1, INT i2) = INT (i1 + i2)
  | add _ = raise TYPE_ERROR;


(* u2e: univ -> exp *)
fun u2e (INT i) = LIT i
  | u2e (FUN f) = LAM (fn e => u2e (f (e2u e)))
(* e2u : exp -> univ *)
and e2u (LIT i) = INT i
  | e2u (LAM f) = FUN (fn u => e2u (f (u2e u)))
  | e2u (APP _) = raise NOT_A_VALUE
  | e2u (ADD _) = raise NOT_A_VALUE

(* eval : exp -> univ *)
fun eval (LIT i) = INT i
  | eval (LAM f) = FUN (fn u => eval (f (u2e u)))
  | eval (APP (e0, e1)) =
    app (eval e0, eval e1)
  | eval (ADD (e0, e1)) =
    add (eval e0, eval e1)
