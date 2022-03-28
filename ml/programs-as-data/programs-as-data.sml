use "dc.sml";
use "cpshierarchy.sml";

(* Chapter 1 *)

(* 1.1.1 Induction and recursion *)

(* One way to define natural numbers:
   n ::= 0 |  n + 1
 *)

fun zerop n = n = 0

fun sub1 n = n - 1

fun power0 (x, n) =
    let fun visit n =
	    if zerop n then 1 else x * visit(sub1 n)
    in visit n
    end

(* Another way to construct natural numbers:
    n ::= 0 | m
    m ::= 2m | 2n + 1
   Based on this we can define a faster exponentiation function:
    x⁰    = 1
    x²ᵐ   = (x²)ᵐ
    x²ⁿ⁺¹ = (x²)ⁿ ∗ x
*)

fun oddp  n = if zerop n then false else evenp (sub1 n)
and evenp n = if zerop n then true  else oddp  (sub1 n)

fun sqr n = n * n

fun divmod2 n = (n div 2, evenp n)

(* block-structured and scope-sensitive *)
fun power1 (x, n) =
    let fun visit n =
            if zerop n then 1
            else visit_positive n
        and visit_positive m =
            let val (q, r) = divmod2 m
            in if r then sqr (visit_positive q)
               else sqr(visit q) * x
            end
    in visit n end

fun power1_fs (x, n) =
    let fun visit n =
	    if zerop n then 1
	    else let val (q, r) = divmod2 n
		 in if r then sqr (visit q)
		    else sqr (visit q) * x
		 end
    in visit n end

(* 1.1.4 Generic Programming *)

fun fold_nat2 (base, even, odd) n =
    let fun visit n =
            if zerop n then base else visit_positive n
        and visit_positive m =
            let val (q, r) = divmod2 m
            in if r then even (visit_positive q)
               else odd (visit q)
            end
    in visit n end

fun power2 (x, n) = fold_nat2 (1, sqr, fn v => sqr(v) * x) n

(* 1.1.5 Divide and Conquer for floating-point numbers *)

(* sin(3x) = 3sin(x) - 4sin(x)^4 *)

fun sin0 (x, eps) =
    let fun visit x =
            if abs x < eps then x
            else let val s = visit (x / 3.0)
                 in 3.0 * s - 4.0 * s * s * s
                 end
    in visit x end

(* 1.1.6 Lazy data structures *)

fun reverse_prepend (nil, a) = a
  | reverse_prepend (x :: xs, a) = reverse_prepend (xs, x :: a)

fun enumerate xs =
    let fun visit (nil, p) = nil
          | visit (x :: xs, p) = (x, reverse_prepend (p, xs)) :: (visit (xs, x :: p))
    in visit (xs, nil) end

fun generate (xs, lazy_nil, lazy_cons) =
    let fun visit (nil, p) = lazy_nil ()
          | visit (x :: xs, p) =
            lazy_cons ((x, reverse_prepend (p, xs)), fn () => visit (xs, x :: p))
    in visit (xs, nil) end

fun enumerate1 xs = generate (xs, fn () => nil, fn (r, t) => r :: t())

(* 1.2 Continuation-passing style *)

fun mul_c (x, y, k) = k (x * y)

fun sqr_c (x, k) = k (x * x)

fun zerop_c (x, yes, no) = if x = 0 then yes () else no ()

fun divmod2_c (x, f, g) =
    let val q = x div 2
    in if evenp x then f q else g q
    end

fun power3 (x, n, k) =
    let fun visit_c (n, k) =
            zerop_c (n,
                     fn () => k 1,
                     fn () => visit_positive_c (n, k))
        and visit_positive_c (m, k) =
            divmod2_c (m,
                       fn q => visit_positive_c (q, fn v => sqr_c (v, k)),
                       fn q => visit_c (q, fn v => sqr_c(v, fn v2 => mul_c(v2, x, k))))
    in visit_c (n, k) end

(* Mixing direct and CPS *)

fun power4 (x, n, k) =
    let fun visit_c (n, k) =
            if zerop n then k 1
            else visit_positive_c (n, k)
        and visit_positive_c (m, k) =
            let val (q, r) = divmod2 m
            in if r then visit_positive_c (q, fn v => k (sqr v))
               else visit_c (q, fn v => k (x * (sqr v)))
            end
    in visit_c (n, k) end

(* Interfacing direct-style word and CPS world *)

fun sin1 (x, eps) =
  let fun visit_c (x, k) =
      if abs x < eps then k x
      else visit_c (x / 3.0, fn s => k (3.0 * s - 4.0 * s * s * s))
  in visit_c (x, fn s => s) end

fun power5(x, n, k) =
  fold_nat2 (fn k => k 1,
             fn c => fn k => c (fn v => k (sqr v)),
             fn c => fn k => c (fn v => k ((sqr v) * x)))
            n k

(* Stopping the computation at any point *)

datatype 'a answer = VALUE of 'a
                   | ERROR of string

fun divmoc_c (i, 0, k) = ERROR ("division of " ^ Int.toString i ^ " by 0")
  | divmoc_c (i, j, k) = k (i div j, i mod j)

(* Continuing the computation eleswhere *)

datatype mobile = OBJ of int
                | BAR of int * mobile * mobile

val m1 = BAR (1, BAR (1, OBJ 2, OBJ 2), OBJ 5) (* balanced *)
val m2 = BAR (1, OBJ 6, BAR (1, OBJ 2, OBJ 9)) (* not balanced *)

(* Challenge: test the balance of a given mobile by traversing it at most once *)

fun bal1 (m, k) =
  let fun visit_c (OBJ n, k') = k' n
        | visit_c (BAR (n, m1, m2), k') =
          visit_c (m1, fn n1 => visit_c (m2, fn n2 => if n1 = n2 then k' (n + n1 + n2)
                                                      else k false))
  in visit_c (m, fn _ => k true) end

(* Summary:
 * 1) the current continuation is invoked explicitly to continue the
 *    computation with an intermediate result.
 * 2) invoking a continuation other than the current one has the effect of
 *    transferring control to this other continuation, never to return to
 *    the current one, as in a jump.
 * 3) not invoking any continuation at all has the effect of stoping the computation.
 *)

fun bal2 m =
  let fun visit (OBJ n) = SOME n
        | visit (BAR (n, m1, m2)) =
          (case visit m1 of
             NONE => NONE
           | SOME n1 => (case visit m2 of
                           NONE => NONE
                         | SOME n2 => if n1 = n2 then SOME (n + n1 + n2)
                                      else NONE))
  in case visit m of
       NONE => false
     | SOME n => true
  end

open SMLofNJ.Cont

(* type 'a cont
 * val callcc : ('a cont -> 'a) -> 'a
 * val throw : 'a cont -> 'a -> 'b
 *)

fun bal3 m =
  callcc (fn k => let fun visit (OBJ n) = n
                        | visit (BAR (n, m1, m2)) =
                            let val n1 = visit m1
                                val n2 = visit m2
                            in if n1 = n2 then n + n1 + n2
                               else throw k false
                            end
                  in let val _ = visit m
                     in true end
                  end)

(* Felleisen's C operator : ('a cont -> 'b) -> void *)
(* fun C f = callcc (fn k => abort (f k)) *)

(* Releasing control *)

fun bal5 m =
  let fun visit_c (OBJ n, k) = k n
        | visit_c (BAR (n, m1, m2), k) =
          visit_c (m1, fn n1 => visit_c (m2, fn n2 => if n1 = n2 then k (n + n1 + n2)
                                                      else false))
  in visit_c (m, fn _ => true) end

(* Regaining control *)
datatype expression = IDE of int
                    | ADD of expression * expression
                    | MUL of expression * expression

datatype product = IDE_PROD of int
                 | MUL_PROD of product * product

datatype sum_of_products = PROD of product
                         | ADD_PROD of sum_of_products * sum_of_products

fun distribute e =
  let (* expression * (product -> sum_of_products) -> sum_of_products *)
     fun visit_c (IDE x, k) = k (IDE_PROD x)
       | visit_c (ADD (e1, e2), k) =
         ADD_PROD (visit_c (e1, k), visit_c (e2, k))
       | visit_c (MUL (e1, e2), k) =
         visit_c (e1, fn p1 => visit_c (e2, fn p2 => k (MUL_PROD (p1, p2))))
  in visit_c (e, fn p => PROD p) end

(* 1.4 2CPS *)

(* The success continuation is the delimited continuation,
 * the failure continuation is the meta continuatin. *)

(* The current delimited continuation is invoked to continue the computation
 *   with an intermediate result and the current meta-continuation;
 * Invoking a delimited continuation other than the current one (and passing
 *   it the current meta-continuation) has the effect of transferring control
 *   to this other delimited continuation, never to return to the current one
 *   (as a jump);
 * Not invoking any delimited continuation (but invoking the current meta-continuation)
 * has the effect of stoping the current delimited computation and the
 * computation beyond the current delimitation.
 *)

structure ControlInt = Control(type ans = int)
open ControlInt

val x = 1 + reset (fn () => 10 + shift (fn k => k 100 + 1000))
val x' = 1 + (let val k = fn v => 10 + v in k 100 + 1000 end)
val x'' = (fn k' => let val k'' = fn v => k' (1 + v)
                    in k'' (let val k = fn v => 10 + v
                            in k 100 + 1000 end)
                    end) (fn x => x)

structure ControlSumProd = Control(type ans = sum_of_products)
open ControlSumProd

fun distrubute_ds e =
  let fun visit (IDE x) = IDE_PROD x
        | visit (ADD (e1, e2)) =
            shift (fn k => ADD_PROD (reset (fn () => k (visit e1)),
                                     reset (fn () => k (visit e2))))
        | visit (MUL (e1, e2)) =
            MUL_PROD (visit e1, visit e2)
  in reset (fn () => PROD (visit e)) end

(* Simulating state with shift/reset *)

datatype tree = LEAF of int
              | NODE of tree * int * tree

fun label_infix0 t =
  let fun inc i = (i, i + 1)
      fun visit (LEAF _, i) = (LEAF i, i + 1)
        | visit (NODE (t1, _, t2), i) =
            let val (t1', i1) = visit (t1, i)
                val (j, i1') = inc i1
                val (t2', i2) = visit (t2, i1')
            in (NODE (t1', j, t2'), i2) end
  in #1 (visit (t, 1)) end

fun label_infix1 t =
  let fun inc ((), k) = fn i => k i (i + 1)
      fun visit (LEAF _, k) = inc ((), fn i => k (LEAF i))
        | visit (NODE (t1, _, t2), k) =
            visit (t1, fn t1' =>
              inc ((), fn j =>
                visit (t2, fn t2' =>
                  k (NODE (t1', j, t2')))))
  in visit (t, fn t' => fn i => t') 1
  end

structure S = Control (type ans = int -> tree)

fun label_infix2 t =
  let fun inc () = S.shift (fn k => fn i => k i (i + 1))
      fun visit (LEAF _) = LEAF (inc ())
        | visit (NODE (t1, _, t2)) = NODE (visit t1, inc (), visit t2)
  in S.reset (fn () => let val t' = visit t in fn i => t' end) 1 end

(* Simulate a state monad *)

structure S = Control (type ans = int -> int list)

fun get () = S.shift (fn k => fn i => k i i)
fun set i' = S.shift (fn k => fn i => k () i')

fun with_int_state (i, t) =
  S.reset (fn () => let val result = t ()
                    in fn i' => result end) i

val v = with_int_state (1, fn () =>
  let val x1 = get ()
      val () = set 10
      val x2 = get ()
      val () = set 100
  in [x1, x2, get ()]
  end)

(* 2CPS version of cryptarithmetic puzzle *)

fun generate2 (ds, sc, fc) =
  let fun visit (nil, a) = fc ()
        | visit (d :: ds, a) = sc (d, reverse_prepend(a, ds), fn () => visit (ds, d :: a))
  in visit (ds, nil) end

fun solve2 (ds, sc, fc) =
  generate2 (ds, fn (d1, ds, fc) =>
    generate2 (ds, fn (d2, ds, fc) =>
      generate2 (ds, fn (d3, ds, fc) =>
        generate2 (ds, fn (d4, ds, fc) =>
          generate2 (ds, fn (d5, ds, fc) =>
            generate2 (ds, fn (d6, ds, fc) =>
              generate2 (ds, fn (d7, ds, fc) =>
                generate2 (ds, fn (d8, ds, fc) =>
                  generate2 (ds, fn (d9, ds, fc) =>
                    let val x1 = 100 * d1 + 10 * d2 + d3
                        val x2 = 100 * d4 + 10 * d5 + d6
                        val x3 = 100 * d7 + 10 * d8 + d9
                    in if x1 + x2 = x3
                       then sc ((x1, x2, x3), fc)
                       else fc ()
                    end,
                  fc),
                fc),
              fc),
            fc),
          fc),
        fc),
      fc),
    fc),
  fc)

type result = (int * int * int) option

fun main_first2 () = solve2 ([1,2,3,4,5,6,7,8,9],
                             fn (t, fc) => SOME t,
                             fn () => NONE)

type result_all = (int * int * int) list

fun main_all2 () = solve2 ([1,2,3,4,5,6,7,8,9],
                           fn (t, fc) => t :: fc (),
                           fn () => nil)

fun main_all_cps () = solve2 ([1,2,3,4,5,6,7,8,9],
                              fn (t, fc) => fn ec => fc () (fn ts => ec (t :: ts)),
                              fn () => fn ec => ec nil)
                             (fn x => x)

type result_cont = int
fun main_count2 () = solve2 ([1,2,3,4,5,6,7,8,9],
                            fn (t, fc) => 1 + fc(),
                            fn () => 0)

(* 1CPS version of cryptarithmetic puzzle *)

(*
fun generate1 (ds, sc) =
  let fun visit (nil, a) = nil
        | visit (d :: ds, a) =
            let val () = sc (d, reverse_prepend (a, ds))
            in visit (ds, d :: a) end
  in visit (ds, nil) end

fun solve1 (ds, sc) =
  generate1 (ds, fn (d1, ds) =>
    generate1 (ds, fn (d2, ds) =>
      generate1 (ds, fn (d3, ds) =>
        generate1 (ds, fn (d4, ds) =>
          generate1 (ds, fn (d5, ds) =>
            generate1 (ds, fn (d6, ds) =>
              generate1 (ds, fn (d7, ds) =>
                generate1 (ds, fn (d8, ds) =>
                  generate1 (ds, fn (d9, ds) =>
                    let val x1 = 100 * d1 + 10 * d2 + d3
                        val x2 = 100 * d4 + 10 * d5 + d6
                        val x3 = 100 * d7 + 10 * d8 + d9
                    in if x1 + x2 = x3 then sc (x1, x2, x3)
                       else () end)))))))))

structure C = ShiftReset (type ans = result)
val shift = C.shift
val reset = C.reset

fun main_first1 () = reset (fn () =>
  let val () = solve1 ([1,2,3,4,5,6,7,8,9], fn t => shift (fn fc => SOME t))
  in NONE end)

structure C = ShiftReset (type ans = result_all)
val shift = C.shift
val reset = C.reset

fun main_all1 () =
  reset (fn () => let val () = solve ([1,2,3,4,5,6,7,8,9],
                                      fn t => shift (fn fc => t :: fc ()))
                  in nil end)
*)

(* Chapter 2 *)

(* To make power1 (section 1.1.3) scope-insensitive, lift x to be a parameter: *)
fun power6 (x, n) =
  let fun visit x n = if zerop n then 1 else visit_positive x n
      and visit_positive x m =
        let val (q, r) = divmod2 m
        in if r then sqr (visit_positive x q)
           else sqr (visit x q) * x
        end
  in visit x n end

(* Further, to make power6 non-block-structured, float the local functions
 * to the same lexicial scope: *)

fun power7_visit x n = if zerop n then 1 else power7_visit_positive x n
and power7_visit_positive x m =
  let val (q, r) = divmod2 m
  in if r then sqr (power7_visit_positive x q)
     else sqr (power7_visit x q) * x
  end
fun power7 (x, n) = power7_visit x n

(* Section 2.2 *)

(* Defunctionalized version of sin1 *)

datatype cont = C0 | C1 of cont
fun apply_cont (C0, s) = s
  | apply_cont (C1 k, s) = apply_cont (k, 3.0 * s - 4.0 * s * s * s)
fun sin2 (x, eps) =
  let fun visit (x, k) = if abs x < eps then apply_cont (k, x)
                         else visit (x / 3.0, C1 k)
  in visit (x, C0) end

(* Higher-order representation of lists *)

val ho_nil = fn ys => ys
val ho_cons = fn y => fn ys => y :: ys

fun generate_ho (xs, lazy_nil, lazy_cons) =
  let (* visit : 'a list * ('a list -> 'a list) -> 'b *)
      fun visit (nil, pc) = lazy_nil ()
        | visit (x :: xs, pc) =
            lazy_cons ((x, pc xs),
                       fn () => visit (xs, fn a => pc (x :: a)))
  in visit (xs, fn x => x) end

(* Defunctionalized version *)

datatype 'a prefix_constructor = PC0 | PC1 of 'a * 'a prefix_constructor

fun apply_prefix_constructor (PC0, a) = a
  | apply_prefix_constructor (PC1 (x, pc), a) =
     apply_prefix_constructor (pc, x :: a)

fun generate_fo_defunc (xs, lazy_nil, lazy_cons) =
  let fun visit (nil, pc) = lazy_nil ()
        | visit (x :: xs, pc) =
            lazy_cons ((x, apply_prefix_constructor (pc, xs)),
                       fn () => visit (xs, PC1 (x, pc)))
  in visit (xs, PC0) end

(* Defunctionalization for transforming programs *)

type cont = int
val d_C0 : cont = 0
val d_C1 : cont -> cont = fn k => k + 1

fun apply_cont (0, s) = s
  | apply_cont (k, s) = apply_cont (k - 1, 3.0 * s - 4.0 * s * s * s)

fun sin3 (x, eps) =
    let fun visit (x, k) =
	    if abs x < eps then apply_cont (k, x)
	    else visit (x / 3.0, d_C1 k)
    in visit (x, d_C0) end

(* Section 2.4 Synergy *)

(* Lightweight defunctionalization *)

datatype cont = C0
	      | C1 of cont
	      | C2 of cont * int

fun apply_cont (C0, v) = v
  | apply_cont (C1 k, v) = apply_cont (k, sqr v)
  | apply_cont (C2 (k, x), v) = apply_cont (k, (sqr v) * x)

fun power8 (x, n) =
    let fun visit_c (n, k) = if zerop n then apply_cont (k, 1)
			     else visit_positive_c (n, k)
	and visit_positive_c (m, k) =
	    let val (q, r) = divmod2 m
	    in if r then visit_positive_c (q, C1 k)
	       else visit_c (q, C2 (k, x))
	    end
    in visit_c (n, C0) end

(* Then transform them into a scope-sensitive form *)

datatype cont = C0
	      | C1 of cont
	      | C2 of cont

fun power9 (x, n) =
    let fun apply_cont (C0, v) = v
	  | apply_cont (C1 k, v) = apply_cont (k, sqr v)
	  | apply_cont (C2 k, v) = apply_cont (k, (sqr v) * x)
	fun visit_c (n, k) =
	    if zerop n then apply_cont (k, 1)
	    else visit_positive_c (n, k)
	and visit_positive_c (m, k) =
	    let val (q, r) = divmod2 m
	    in if r then visit_positive_c (q, C1 k)
	       else visit_c (q, C2 k) end
    in visit_c (n, C0) end

(* One can also use native ML integers to represent data continuations: *)

type cont = int
val C0_int: cont = 1
val C1_int: int -> cont = fn k => 2 * k
val C2_int: int -> cont = fn k => 2 * k + 1

fun power10 (x, n) =
    let fun apply_cont (1, v) = v
	  | apply_cont (k, v) =
	    let val (k', r) = divmod2 k
	    in if r
	       then apply_cont (k', sqr v)
	       else apply_cont (k', (sqr v) * x)
	    end
	fun visit_c (n, k) =
	    if zerop n
	    then apply_cont (k, 1)
	    else visit_positive_c (n, k)
	and visit_positive_c (m, k) =
	    let val (q, r) = divmod2 m
	    in if r then visit_positive_c (q, C1_int k)
	       else visit_c (q, C2_int k)
	    end
    in visit_c (n, C0_int) end

(* Two alternative fast exponentiation functions *)

type cont = int list
val C0_lst = nil
val C1_lst = fn (k, y) => y :: k

fun apply_cont (nil, v) = v
  | apply_cont (y :: k, v) = apply_cont (k, v * y)

(* use a list of ints, i.e, power1_alt', page 51 *)
fun power11 (x, n) =
    let fun visit (y, n, k) = if zerop n then apply_cont (k, 1)
			      else visit_positive (y, n, k)
	and visit_positive (y, m, k) =
	    let val (q, r) = divmod2 m
	    in if r then visit_positive (sqr y, q, k)
	       else visit (sqr y, q, C1_lst (k, y))
	    end
    in visit (x, n, C0_lst) end

(* Use an accumulator *)

fun power12 (x, n) =
    let fun visit (y, n, a) =
	    if zerop n then a
	    else visit_positive (y, n, a)
	and visit_positive (y, m, a) =
	    let val (q, r) = divmod2 m
	    in if r then visit_positive (sqr y, q, a)
	       else visit (sqr y, q, y * a)
	    end
    in visit (x, n, 1) end

(* Section 3, Program execution *)

