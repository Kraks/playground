datatype person = King
                | Peer of string * string * int
                | Knight of string
                | Peasant of string;

King;
Peer("Earl", "Carlisle", 7);
Knight "Kraks";

fun title King = "His majesty the King"
  | title (Peer(deg, terr, _)) = "The " ^ deg ^ " of " ^ terr
  | title (Knight name) = "Sir " ^ name
  | title (Peasant name) = name;

fun title2 p =
  case p of
       King => "His majesty the King"
     | Peer(deg, terr, _) => "The " ^ deg ^ " of " ^ terr
     | Knight name => "Sir " ^ name
     | Peasant name => name;

fun sirs [] = []
  | sirs ((Knight s)::ps) = s :: (sirs ps)
  | sirs (p::ps) = (sirs ps);

datatype degree = Duke
                | Marquis
                | Earl
                | Viscount
                | Baron;


(* datatype bool = false | true; *)
fun not false = true
  | not true = false;

(* 4.3 *)
datatype 'a option = NONE | SOME of 'a;

Real.fromString "4.0E5"; (* SOME 4.0 *)

(* disjoint sum / union*)
datatype ('a, 'b) sum = In1 of 'a | In2 of 'b;

(* concatenate all strings in In1 *)
fun concat1 [] = ""
  | concat1 ((In1 s)::l) = s ^ concat1 l
  | concat1 ((In2 _)::l) = concat1 l;

fun merge(xlist, ylist): real list =
  case xlist of
       []    => ylist
     | x::xs => (case ylist of
                      []    => xlist
                    | y::ys => if x <= y then x::merge(xs, ylist)
                               else y::merge(xlist, ys));

exception Failure;
exception Failedbecause of string;
exception Badvalue of int;

exception Empty;
fun hd (x::_) = x
  | hd []     = raise Empty

fun tl (_::xs) = xs
  | tl []      = raise Empty

exception Subscript;
fun nth(x::_, 0)  = x
  | nth(x::xs, n) = if n > 0 then nth(xs, n-1)
                    else raise Subscript
  | nth _         = raise Subscript

exception Change
fun backChange (coinvals, 0)         = []
  | backChange ([], amount)          = raise Change
  | backChange (c::coinvals, amount) =
    if amount < 0 then raise Change
    else c::backChange(c::coinvals, amount-c)
    handle Change => backChange(coinvals, amount);

(* TREE *)

(* binary tree *)
datatype 'a tree = Lf
                 | Br of 'a * 'a tree * 'a tree;

val birnam =
  Br("The", Br("woord", Lf, Br ("of", Br ("Birnam", Lf, Lf), Lf)), Lf);

fun size Lf = 0
  | size (Br(v, t1, t2)) = 1 + size t1 + size t2;

fun depth Lf = 0
  | depth (Br(v, t1, t2)) = 1 + Int.max(depth t1, depth t2);

(* Complete tree *)
fun comptree (k, n) =
  if n = 0 then Lf
  else Br(k, comptree(2*k, n-1),
             comptree(2*k+1, n-1));

fun reflect Lf              = Lf
  | reflect (Br(v, t1, t2)) = Br(v, reflect t2, reflect t1);

fun preorder Lf              = []
  | preorder (Br(v, t1, t2)) = [v] @ preorder t1 @ preorder t2;

fun inorder Lf              = []
  | inorder (Br(v, t1, t2)) = inorder t1 @ [v] @ inorder t2;

fun postorder Lf              = []
  | postorder (Br(v, t1, t2)) = postorder t1 @ postorder t2 @ [v];

fun preord (Lf, vs) = vs
  | preord (Br(v, t1, t2), vs) = v::preord(t1, preord(t2, vs));

fun inord (Lf, vs) = vs
  | inord (Br(v, t1, t2), vs) = inord(t1, v::inord(t2, vs));

fun postord (Lf, vs) = vs
  | postord (Br(v, t1, t2), vs) = postord(t1, postord(t2, v::vs));

(* create a balanced tree from preordered list *)
fun balpre [] = Lf
  | balpre(x::xs) =
    let val k = length xs div 2
    in
      Br(x, balpre(List.take(xs, k)), balpre(List.drop(xs, k)))
    end;

fun balin [] = Lf
  | balin xs =
    let val k = length xs div 2
        val y::ys = List.drop(xs, k)
    in
      Br(y, balin(List.take(xs, k)), balin ys)
    end;

fun balpost [] = Lf
  | balpost xs =
    let
      val x = hd(rev xs)
      val k = ((length xs) - 1) div 2
      val ys = List.take(xs, (length xs)-1)
    in
      Br(x, balpost(List.take(ys, k)), balpost(List.drop(ys, k)))
    end;

(* 4.15 functional array *)

fun sub (Lf, _) = raise Subscript
  | sub (Br(v, t1, t2), k) =
    if k = 1 then v
    else if k mod 2 = 0
         then sub(t1, k div 2)
         else sub(t2, k div 2);

fun update (Lf, k, w) =
    if k = 1 then Br(w, Lf, Lf)
    else raise Subscript
  | update (Br(v, t1, t2), k, w) =
    if k = 1 then Br(w, t1, t2)
    else if k mod 2 = 0
         then Br(v, update(t1, k div 2, w), t2)
         else Br(v, t1, update(t2, k div 2, w));

fun delete (Lf, n) = raise Subscript
  | delete (Br(v, t1, t2), n) =
    if n = 1 then Lf
    else if n mod 2 = 0
         then Br(v, delete(t1, n div 2), t2)
         else Br(v, t1, delete(t2, n div 2));

(* extent the tree from root *)
fun loext (Lf, w) = Br(w, Lf, Lf)
  | loext (Br(v, t1, t2), w) = Br(w, loext(t2, v), t1);

exception Size;
fun lorem Lf = raise Size
  | lorem (Br(_, Lf, Lf)) = Lf
  | lorem (Br(_, t1 as Br(v, _, _), t2)) = Br(v, t2, lorem t1);

(* test flex array *)
loext(Lf, "A");
loext(it, "B");
loext(it, "C");
loext(it, "D");
val tlet = loext(it, "E");
val tdag = update(update(tlet, 5, "Amen"), 2, "dagger");


(* 4.16 priority queue *)

signature PRIORITY_QUEIE =
sig
  type item
  type t
  val empty     : t
  val null      : t -> bool
  val insert    : item * t -> t
  val min       : t -> item
  val delmin    : t -> t
  val fromList  : item list -> t
  val toList    : t -> item list
  val sort      : item list -> item list
end;

structure Heap : PRIORITY_QUEIE =
struct
  type item = real;
  type t = item tree;

  val empty = Lf;

  fun null Lf = true
    | null (Br _) = false;

  fun min (Br(v, _, _)) = v;

  fun insert(w: real, Lf) = Br(w, Lf, Lf)
    | insert(w, Br(v, t1, t2)) =
      if w <= v then Br(w, insert(v, t2), t1)
                else Br(v, insert(w, t2), t1);

  fun leftrem(Br(v, Lf, Lf)) = (v, Lf)
    | leftrem(Br(v, t1, t2)) =
      let val (w, t) = leftrem t1
      in (w, Br(v, t2, t)) end;

  fun siftdown (w: real, Lf, Lf) = Br(w, Lf, Lf)
    | siftdown (w, t as Br(v, Lf, Lf), Lf) =
      if w <= v then Br(w, t, Lf)
                else Br(v, Br(w, Lf, Lf), Lf)
    | siftdown (w, t1 as Br(v1, p1, q1), t2 as Br(v2, p2, q2)) =
      if w <= v1 andalso w <= v2 then Br(w, t1, t2)
      else if v1 <= v2 then Br(v1, siftdown(w, p1, q1), t2)
                       else Br(v2, t1, siftdown(w, p2, q2));

  fun delmin Lf = raise Size
    | delmin (Br(v, Lf, _)) = Lf
    | delmin (Br(v, t1, t2)) =
      let val (w, t) = leftrem t1
      in siftdown(w, t2, t) end;

  fun heapify (0, vs) = (Lf, vs)
    | heapify (n ,v::vs) =
      let val (t1, vs1) = heapify(n div 2, vs)
          val (t2, vs2) = heapify((n-1) div 2, vs1)
      in (siftdown(v, t1, t2), vs2) end;

  fun  fromList vs = #1 (heapify (length vs, vs));

  fun toList (t as Br(v, _, _)) = v :: toList(delmin t)
    | toList Lf                 = [];

  fun sort vs = toList (fromList vs);
end;


(* tautology *)
datatype prop = Atom of string
              | Neg of prop
              | Conj of prop * prop
              | Disj of prop * prop;

fun implies (p, q) = Disj(Neg p, q);

val rich    = Atom "rich";
val landed  = Atom "landed";
val saintly = Atom "saintly";
val assumption1 = implies(landed, rich);
val assumption2 = Neg(Conj(saintly, rich));
val concl = Disj(Neg(Atom "landed"), Neg(Atom "saintly"));
val goal = implies(Conj(assumption1, assumption2), concl);

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

fun nnfpos (Atom a)         = Atom a
  | nnfpos (Neg p)          = nnfneg p
  | nnfpos (Conj(p, q))     = Conj(nnfpos p, nnfpos q)
  | nnfpos (Disj(p, q))     = Disj(nnfpos q, nnfpos q)
and nnfneg (Atom a)         = Neg (Atom a)
  | nnfneg (Neg p)          = nnfpos p
  | nnfneg (Conj(p, q))     = Disj(nnfneg p, nnfneg q)
  | nnfneg (Disj(p, q))     = Conj(nnfneg p, nnfneg q);

(* Conjunctive normal form
*  p|(q&r) -> (p|q)&(p|r)
*  (q&r)|p -> (q|p)&(r|p)
*)

(* distrib compute CNF of p|q, if p and q are both CNF *)
fun distrib (p, Conj(q, r)) = Conj(distrib(p, q), distrib(p, r))
  | distrib (Conj(q, r), p) = Conj(distrib(q, p), distrib(r, p))
  | distrib (p, q)          = Disj(p, q);

fun cnf (Conj(p, q)) = Conj(cnf p, cnf q)
  | cnf (Disj(p, q)) = distrib (cnf p, cnf q)
  | cnf p            = p;

val cgoal = cnf (nnf goal);

exception NonCNF;

fun positives (Atom a)         = [a]
  | positives (Neg (Atom _))    = []
  | positives (Disj(p, q))     = positives p @ positives q
  | positives _                = raise NonCNF;

fun negatives (Atom _)         = []
  | negatives (Neg(Atom a))    = [a]
  | negatives (Disj(p, q))     = negatives p @ negatives q
  | negatives _                = raise NonCNF;

infix mem;
fun (x mem [])      = false
  | (x mem (y::ys)) = (x=y) orelse (x mem ys);

fun inter([], ys)    = []
  | inter(x::xs, ys) = if x mem ys then x::inter(xs, ys)
                                   else inter(xs, ys);

fun taut (Conj(p, q)) = taut p andalso taut q
  | taut p            = not (null(inter(positives p, negatives p)));
