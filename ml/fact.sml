(* Factorial *)

(* fac_c : int * (int -> 'a) -> 'a *)
fun fac_c (0, k) = k 1
  | fac_c (n, k) = fac_c (n-1, fn v => k (n * v))

fun fact n = fac_c (n, fn v => v)

datatype cont = CONT0
              | CONT1 of int * cont

(* apply_cont : cont * int -> int *)
fun apply_cont (CONT0, v) = v
  | apply_cont (CONT1 (n, k), v) = apply_cont (k, n * v)

(* A list representation of cont *)
type cont_list = int list
fun apply_cont_list (nil, v) = v
  | apply_cont_list (n :: k, v) = apply_cont_list (k, n * v)

fun fac_c' (0, k) = apply_cont_list (k, 1)
  | fac_c' (n, k) = fac_c' (n-1, n :: k)

fun fact' n = fac_c' (n, nil)
