(* 4.14 Dictionary *)

signature DICTIONARY =
sig
  type key
  type 'a t
  exception E of key
  val empty  : 'a t
  val lookup : 'a t * key -> 'a
  val insert : 'a t * key * 'a -> 'a t
  val update : 'a t * key * 'a -> 'a t
end;

datatype 'a tree = Lf
                 | Br of 'a * 'a tree * 'a tree;

structure Dict : DICTIONARY =
struct

  type key = string;
  type 'a t = (key * 'a) tree;

  exception E of key;

  val empty = Lf;
  fun lookup (Lf, b)                 = raise E b
    | lookup (Br((a, x), t1, t2), b) =
      (case String.compare(a, b) of
            GREATER => lookup(t1, b)
          | EQUAL   => x
          | LESS    => lookup(t2, b));

  fun insert (Lf, b, y)                 = Br((b, y), Lf, Lf)
    | insert (Br((a, x), t1, t2), b, y) =
      (case String.compare(a, b) of
            GREATER => Br((a, x), insert(t1, b, y), t2)
          | EQUAL   => raise E b
          | LESS    => Br((a, x), t1, insert(t2, b, y)));

  fun update (Lf, b, y)                 = Br((b, y), Lf, Lf)
    | update (Br((a, x), t1, t2), b, y) = 
      (case String.compare(a, b) of 
            GREATER => Br((a, x), update(t1, b, y), t2)
          | EQUAL   => Br((a, y), t1, t2)
          | LESS    => Br((a, x), t1, update(t2, b, y)));
end;

val t = Dict.insert(Lf, "France", 33);
val t = Dict.insert(t, "Egypt", 20);
val t = Dict.update(t, "France", 40);

(* balance it 
  val xs = inord(tree, []);
  val tree = balin xs;
*)


