Require Import Reals.
Require Import Psatz.
Open Scope R_scope.

Goal forall (r1 r2 : R), r1 < r2 <-> exists s, s > 0 /\ r1 + s = r2.
Proof.
  intros.
  split.
  - intros. exists (r2 - r1). split.
    lra. lra.
  - intros. destruct H. lra.
Qed.
