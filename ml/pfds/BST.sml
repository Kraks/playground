(* Section 2.2 *)

signature SET =
sig
    type Elem
    type Set
    val empty : Set
    val insert : Elem * Set -> Set
    val member : Elem * Set -> bool
end;

signature ORDERED =
sig
    type T
    val eq  : T * T -> bool
    val lt  : T * T -> bool
    val leq : T * T -> bool
end

functor UnbalancedSet(Element : ORDERED) : SET =
struct
    type Elem = Element.T
    datatype Tree = E | T of Tree * Elem * Tree
    type Set = Tree

    val empty = E
    fun member (x, E) = false
      | member (x, T (lhs, y, rhs)) =
        if Element.lt (x, y) then member (x, lhs)
        else if Element.lt (y, x) then member (x, rhs)
        else true
    (* Exercise 2.2
     * Rewrite member to take no more than d+1 comparisons (where d is the
     * depth of the tree) by keeping track of a candidate element that might be
     * equal to the query element and checking for equality only when you hit
     * the bottom of the tree. *)
    (* fun member_ex *)
    (* Exercise 2.3 *)
    fun insert (x, E) = T (E, x, E)
      | insert (x, s as T (lhs, y, rhs)) =
        if Element.lt (x, y) then T (insert (x, lhs), y, rhs)
        else if Element.lt (y, x) then T (lhs, y, insert (x, rhs))
        else s
end

(********************************************)

structure IntOrd : ORDERED =
struct
    type T = int
    val eq = (op =)
    val lt = (op <)
    val leq = (op <=)
end
structure IntSet = UnbalancedSet (IntOrd)

fun generate n = let
    fun generate_aux (0, tree) = IntSet.insert (0, tree)
      | generate_aux (x, tree) = generate_aux (x-1, IntSet.insert (x, tree))
in generate_aux (n, IntSet.empty) end

val t10 = generate 10
val should_true = IntSet.member (10, t10)
val should_false = IntSet.member (11, t10)
