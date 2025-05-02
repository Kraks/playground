(* Dyck word recoginizer *)
datatype paren = L | R;
datatype nat = ZERO | SUCC of nat;
type word = paren list;

(* recog : word -> bool *)
fun recog ps =
    (* run : word * nat -> bool *)
    let fun run ([], ZERO)      = true
          | run ([], SUCC c)    = false
          | run (L::ps, c)      = run (ps, SUCC c)
          | run (R::ps, ZERO)   = false
          | run (R::ps, SUCC c) = run (ps, c)
    in run (ps, ZERO)
    end;

fun recog_disentangled ps =
    let (*  run : word * nat -> bool *)
        fun run ([], c)    = run_nil c
          | run (L::ps, c) = run (ps, SUCC c)
          | run (R::ps, c) = run_par (c, ps)
        (*  run_nil : nat -> bool *)
        and run_nil ZERO     = true
          | run_nil (SUCC n) = false
        (*  run_par : nat * word -> bool *)
        and run_par (ZERO, ps)   = false
          | run_par (SUCC c, ps) = run (ps, c)
    in run (ps, ZERO)
    end;

fun recog_merged ps =
    let (*  run : word * nat -> bool *)
        fun run ([], c)    = run_aux (c, NONE)
          | run (L::ps, c) = run (ps, SUCC c)
          | run (R::ps, c) = run_aux (c, SOME ps)
        (*  run_aux : nat * word option -> bool *)
        and run_aux (ZERO, NONE)       = true
          | run_aux (SUCC c, NONE)     = false
          | run_aux (ZERO, SOME ps)    = false
          | run_aux (SUCC c, SOME ps) = run (ps, c)
    in run (ps, ZERO)
    end;

fun recog_refunc ps =
    let (*  run : word * (word option -> bool) -> bool *)
        fun run ([], c) = c NONE
          | run (L::ps, c) = run (ps, fn NONE => false
                                       | SOME ps => run (ps, c))
          | run (R::ps, c) = c (SOME ps)
    in run (ps, fn NONE => true
              | SOME ps => false)
    end;
