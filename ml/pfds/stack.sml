(* Section 2.1 *)

signature STACK =
sig
    type 'a Stack
    val empty   : 'a Stack
    val isEmpty : 'a Stack -> bool
    val cons : 'a * 'a Stack -> 'a Stack
    val head : 'a Stack -> 'a
    val tail : 'a Stack -> 'a Stack
end;

structure List : STACK =
struct
    type 'a Stack = 'a list
    val empty = []
    fun isEmpty s = null s
    fun cons (x, s)= x::s
    fun head s = hd s
    fun tail s = tl s
end;

structure CustomStack : STACK =
struct
    datatype 'a Stack = Nil | Cons of 'a * 'a Stack
    val empty = Nil
    fun isEmpty Nil = true
      | isEmpty _   = false
    fun cons (x, s) = Cons (x, s)
    fun head Nil = raise Empty
      | head (Cons (x, s)) = x
    fun tail Nil = raise Empty
      | tail (Cons (x, s)) = s
end;

fun update ([], i, y) = raise Subscript
  | update (x::xs, 0, y) = y::xs
  | update (x::xs, i, y) = update (xs, i-1, y);

(* Exercise 2.1
 * Write a function suffixes of type 'a list -> 'a list list that
 * takes a list xs and returns a list of all the suffixes of xs in
 * decreasing order of length. *)
fun suffixes [] = [[]]
  | suffixes (x::xs) = [x::xs] @ suffixes xs

(*******************************************)

val mt = CustomStack.empty
val s1 = CustomStack.cons (1, mt)
val s2 = CustomStack.cons (2, s1)
val two = CustomStack.head s2
