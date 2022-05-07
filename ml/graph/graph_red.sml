datatype atom = I | K | S | Y
datatype node = C of atom | A of graph * graph
withtype graph = node ref

datatype stack = EMPTY
               | PUSH of graph * stack
               | MARK of graph * stack

(* setptr : stack * graph -> unit *)
fun setptr (EMPTY, g) 
    = ()
  | setptr (PUSH (r as ref (A (_, g1)), _), g)
    = r := A (g, g1)
  | setptr (MARK (r as ref (A (g0, _)), _), g)
    = r := A (g0, g)

(* unwind : graph * stack -> graph *)
fun unwind (g as ref (A (g0, g1)), gs)
    = unwind (g0, PUSH (g, gs))
  | unwind (g as ref (C a), gs)
    = apply (a, g, gs)
(* atom * graph * stack -> graph *)
and apply (I, _, PUSH (r as ref (A (_, x)), gs))
    = (setptr (gs, x);
       unwind (x, gs))
  | apply (K, _, PUSH (ref (A (_, x)), PUSH (r as ref (A (_, y)), gs)))
    = (r := A (ref (C I), x);
       setptr (gs, x);
       unwind (x, gs))
  | apply (S, _, PUSH (ref (A (_, x)), PUSH (ref (A (_, y)), PUSH (r as ref (A (_, z)), gs))))
    = (r := A (ref (A (x, z)), ref (A (y, z)));
       unwind (r, gs))
  | apply (Y, _, PUSH (r as ref (A (_, x)), gs))
    = (r := A (x, r);
       unwind (r, gs))
  | apply (_, g, gs)
    = continue (gs, g)
(* continue : stack * graph -> graph *)
and continue (EMPTY, g)
    = g
  | continue (PUSH (g as ref (A (_, g1)), gs), _)
    = unwind (g1, MARK (g, gs))
  | continue (MARK (g, gs), _)
    = continue (gs, g)

(* normalize : graph -> graph *)
fun normalize g = unwind (g, EMPTY)
