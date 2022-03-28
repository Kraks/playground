exception NonCNF;

infix mem;
fun (x mem [])      = false
  | (x mem (y::ys)) = (x=y) orelse (x mem ys);

fun inter([], ys)    = []
  | inter(x::xs, ys) = if x mem ys then x::inter(xs, ys)
                                   else inter(xs, ys);

datatype prop = Atom of string
              | Neg of prop
              | Conj of prop * prop
              | Disj of prop * prop;

fun implies (p, q) = Disj(Neg p, q);

fun show (Atom a)     = a
  | show (Neg p)      = "(~" ^ show p ^ ")"
  | show (Conj(p, q)) = "(" ^ show p ^ " & " ^ show q ^ ")"
  | show (Disj(p, q)) = "(" ^ show p ^ " | " ^ show q ^ ")";

(* Negatoin normal form 
*  ~~p -> p
*  ~(p&q) -> ~p | ~q
*  ~(p|q) -> ~p & ~q
*)

fun nnf (Atom a)            = Atom a
  | nnf (Neg (Atom a))      = Neg (Atom a)
  | nnf (Neg (Neg p))       = nnf p
  | nnf (Neg (Conj(p, q)))  = nnf(Disj(Neg p, Neg q))
  | nnf (Neg (Disj(p, q)))  = nnf(Conj(Neg p, Neg q))
  | nnf (Conj(p, q))        = Conj(nnf p, nnf q)
  | nnf (Disj(p, q))        = Disj(nnf p, nnf q); 

(* Conjunctive normal form 
*  p|(q&r) -> (p|q)&(p|r)
*  (q&r)|p -> (q|p)&(r|p)
*)

(* function distrib compute CNF of p|q, if p and q are both CNF *)
fun distrib (p, Conj(q, r)) = Conj(distrib(p, q), distrib(p, r))
  | distrib (Conj(q, r), p) = Conj(distrib(q, p), distrib(r, p))
  | distrib (p, q)          = Disj(p, q);

fun cnf (Conj(p, q)) = Conj(cnf p, cnf q)
  | cnf (Disj(p, q)) = distrib (cnf p, cnf q)
  | cnf p            = p;

fun positives (Atom a)         = [a]
  | positives (Neg (Atom _))    = []
  | positives (Disj(p, q))     = positives p @ positives q
  | positives _                = raise NonCNF;

fun negatives (Atom _)         = []
  | negatives (Neg(Atom a))    = [a]
  | negatives (Disj(p, q))     = negatives p @ negatives q
  | negatives _                = raise NonCNF;

fun taut (Conj(p, q)) = taut p andalso taut q
  | taut p            = not (null(inter(positives p, negatives p)));

val rich    = Atom "rich";
val landed  = Atom "landed";
val saintly = Atom "saintly";
val assumption1 = implies(landed, rich);
val assumption2 = Neg(Conj(saintly, rich));
val concl = Disj(Neg(Atom "landed"), Neg(Atom "saintly"));
val goal = implies(Conj(assumption1, assumption2), concl);
val cgoal = cnf (nnf goal);
taut cgoal;
