(* Insertion sort algorithm in Standard ML *)
fun ins (n, []) = [n]
  | inc (n, ns as h::t) = 
      if n < h then n::ns 
      else h::(ins(n, t));
val insertionSort = List.fordr ins [];

(* Another insertion sort *)
fun insert (x, []): real list = [x]
  | insert (x, y::ys) = 
    if x <= y then x::y::ys
              else y::ins(x, ys);

fun insertion-sort [] = []
  | insertion-sort (x::xs) = insert(x, insertion-sort xs);

(* Quick sort algorithm in Standard ML *)

fun quick [] = []
	| quick [x] = [x]
	| quick (x::xs) = 
		let fun partition (left, right, [])    = (quick left) @ (x :: quick right)
					| partition (left, right, y::ys) = 
              if  y <= x then partition (y::left, right, ys) 
              else partition (left, y::right, ys)
		in partition ([], [], xs) end;
