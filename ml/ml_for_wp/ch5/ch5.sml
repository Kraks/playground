val double = fn n => n*2;
(* if E then E1 else E2
*  (fn true => E1 | false E2)(E)
*)

(* 5.2 Curry function *)
fun prefix pre =
  let fun cat post = pre ^ post
  in cat end;

fun prefix pre post = pre ^ post;

fun replist n x = if n = 0 then []
                  else x::replist (n-1) x;

fun insort lessequal =
  let
    fun ins (x, []) = [x]
      | ins (x, y::ys) =
          if lessequal(x, y) then x::y::ys
          else y::ins(x, ys)
    fun sort [] = []
      | sort (x::xs) = ins(x, sort xs)
  in sort end;

fun leq_stringpair ((a, b), (c, d): string * string) =
  a < c orelse (a = c andalso b <= d);

fun summation f m =
  let fun sum(i, z): real =
      if i=m then z else sum(i+1, z+(f i))
  in sum(0, 0.0) end;

summation (fn k => real(k*k)) 10;

(* 5.5 section *)
fun secl x f y = f(x, y);
fun secr f x y = f(x, y);

val knightify = (secl "Sir " op^);
val recip = (secl 1.0 op/);
val halve = (secr op/ 2.0);

(* 5.6 combinator *)
infix o;
fun (f o g) x = f (g x);

fn x => ~(Math.sqrt x);           (* ~ o Math.sqrt *)
fn a => "beginning" ^ a ^ "end";  (* (secl "beginning" op^) o (secr op^ "end") *)
fn x => 2.0 / (x - 1.0);          (* (secl 2.0 op/) o (secr op- 1.0) *)

summation (Math.sqrt o real) 10;

fun I x = x;        (* S K K*)

fun K x y = x;
summation (K 7.0) 5;

fun S x y z = x z (y z);

(* 5.7 map and filter *)

fun map f [] = []
  | map f (x::xs) = (f x) :: map f xs;

fun filter pred [] = []
  | filter pred (x::xs) =
      if pred x then x :: filter pred xs
                else      filter pred xs;

map (map double) [[1], [2, 3], [4, 5, 6]];
map (map (implode o rev o explode))
    [["When", "he", "shall", "split"], ["thy", "very", "heart", "with", "sorrow"]];

map (filter (secr op< "m"))
    [["my", "hair", "doth", "stand"], ["to", "hear", "her"]];

fun transp ([]::_) = []
  | transp rows    = map hd rows :: transp (map tl rows);

infix mem;
fun ([] mem x)      = false         (* trick: swap the parameters *)
  | ((y::ys) mem x) = (x=y) orelse (ys mem x);

fun inter (xs, ys) = filter (secr (op mem) ys) xs;

(* 5.8 takewhile and dropwhile *)
fun takewhile pred [] = []
  | takewhile pred (x::xs) =
    if pred x then x :: takewhile pred xs
              else [];

fun dropwhile pred [] = []
  | dropwhile pred (x::xs) =
    if pred x then dropwhile pred xs
              else x::xs;

(* 5.9 exists and all *)
fun exists pred [] = false
  | exists pred (x::xs) =
    (pred x) orelse exists pred xs;

fun all pred [] = true
  | all pred (x::xs) = (pred x) andalso all pred xs;

fun x mem xs = exists (secr op= x) xs;

(* disjoint, test two lists are not contain same elements *)
fun disjoint (xs, ys) = all (fn x => all (fn y => x <> y) ys) xs;

(* 5.10 foldl and foldr *)
fun foldl f e [] = e
  | foldl f e (x::xs) = foldl f (f(x, e)) xs;

fun foldr f e [] = e
  | foldr f e (x::xs) = f(x, foldr f e xs);

val sum = foldl op+ 0;

foldl (fn (ns, n) => foldl op+ n ns) 0 [[1], [2, 3], [4, 5, 6]];

foldl op:: [] (explode "Richard");  (* reverse function *)

foldl (fn (_, n) => n + 1) 0 (explode "Margaret"); (* length *)

foldr op:: ["out", "thee"] ["And", "leave"]; (* append *)

foldr op@ [] [[1], [2, 3], [4, 5, 6]]; (* concatenate *)

fun cartprod (xs, ys) =
    foldr (fn (x, pairs) => foldr (fn (y, l) => (x, y)::l) pairs ys)
    [] xs;

(* more recursive combinators *)
fun repeat f n x =
    if n > 0 then repeat f (n-1) (f x)
             else x;

(* binary tree *)
datatype 'a tree = Lf
                 | Br of 'a * 'a tree * 'a tree;
repeat (fn t => Br("No", t, t)) 3 Lf;

fun factaux (k, p) = (k + 1, k * p);
repeat factaux 5 (1, 1);

fun treefold f e Lf = e
  | treefold f e (Br(u, t1, t2)) = f(u, treefold f e t1, treefold f e t2);

fun treeSize t = treefold (fn(_,c1,c2) => 1+c1+c2) 0 t;

fun treeDepth t = treefold (fn(_,d1,d2) => 1 + Int.max(d1, d2)) 0 t;

fun treeReflect t = treefold (fn(u,t1,t2) => Br(u,t2,t1)) Lf t;

fun treePreOrder t = treefold (fn(u,t1,t2) => [u] @ t1 @ t2) [] t;

(* item *)
datatype term = Var of string
              | Fun of string * term list;

(* (x + y) - (y * x) *)
val tm = Fun("-", [Fun("+", [Var "x", Var "u"]),
                   Fun("*", [Var "y", Var "x"])]);

fun subst f (Var a) = f a
  | subst f (Fun (a, args)) = Fun(a, map (subst f ) args);

fun vars (Var a) = [a]
  | vars (Fun (a, args)) = List.concat (map vars args);

fun accumVars (Var a, bs) = a :: bs
  | accumVars (Fun (_, args), bs) = foldr accumVars bs args;

fun replace t a b = if a=b then t else Var b;

subst (replace (Fun("-", [Var "z"])) "x") tm;

(* sequence, or stream *)

datatype 'a seq = Nil
                | Cons of 'a * (unit -> 'a seq);

structure Seq =
struct

  exception Empty;

  fun cons (x, xq) = Cons(x, fn()=>xq);

  fun null Nil = true
    | null _   = false;

  fun hd (Cons(x, xf)) = x
    | hd Nil           = raise Empty;

  fun tl (Cons(x, xf)) = xf
    | tl Nil           = raise Empty;

  fun fromList l = List.foldr cons Nil l;

  fun toList Nil = []
    | toList (Cons(x, xf)) = x :: toList(xf());

  fun take (xq, 0) = []
    | take (Nil, n) = raise Subscript
    | take (Cons(x, xf), n) = x :: take(xf(), n-1);

  fun drop (xq, 0) = xq
    | drop (Nil, n) = raise Subscript
    | drop (Cons(x, xf), n) = drop(xf(), n-1);

  infix @;
  fun Nil @ yq = yq
    | (Cons(x, xf)) @ yq = Cons(x, fn() => (xf()) @ yq);

  fun interleave (Nil, yq) = yq
    | interleave (Cons(x, xf), yq) = Cons(x, fn() => interleave(yq, xf()));

  fun map f Nil = Nil
    | map f (Cons(x, xf)) = Cons(f x, fn() => map f (xf()));

  fun filter pred Nil = Nil
    | filter pred (Cons(x, xf)) =
      if pred x then Cons(x, fn() => filter pred (xf()))
                else filter pred (xf());

  fun iterates f x = Cons(x, fn() => iterates f (f x));

  fun from k = Cons (k, fn() => from(k + 1));

  fun squares Nil : int seq = Nil
    | squares (Cons(x, xf)) = Cons(x*x, fn() => squares(xf()));

  fun add (Cons(x, xf), Cons(y, yf)) = Cons(x+y, fn() => add(xf(), yf()))
    | add _ : int seq = Nil;

end;

local val a = 16807.0 and m = 2147483647.0
  fun nextRand seed =
    let val t = a * seed in
      t - m * real(floor(t/m))
    end
in
  fun randseq s = Seq.map (secr op/ m)
                          (Seq.iterates nextRand (real s))
end;

fun sift p = Seq.filter (fn n => n mod p <> 0);
fun sieve (Cons(p, nf)) = Cons(p, fn() => sieve (sift p (nf())));
val primes = sieve(Seq.from 2);
val primesList = Seq.take (primes, 20);

(* numerical computing *)

(* interleave and seq of seq *)
