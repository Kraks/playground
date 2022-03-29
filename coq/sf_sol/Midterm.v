(*
Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
| singleton: appears_in a (cons a nil)
| left: forall l l1, appears_in a l -> appears_in a (l1++l)
| right: forall l l1, appears_in a l -> appears_in a (l++l1).

Example ex1: appears_in 3 [1;3;2;4].
Proof.
  apply (left 3 [3;2;4] [1]).
  apply (right 3 [3] [2;4]).
  apply singleton.
Qed.
*)
