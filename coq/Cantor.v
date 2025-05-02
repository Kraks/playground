Set Implicit Arguments.
Unset Strict Implicit.
Require Import Coq.micromega.Lia.
Require Import List.
Import ListNotations.

Definition surjective (X Y : Type) (f : X -> Y) : Prop :=
  forall y, exists x, f x = y.

Theorem Cantor X : ~ exists f : X -> X -> Prop,
  surjective f.
Proof.
  intros [f A].
  pose (g := fun x => ~ f x x).
  destruct (A g) as [x B].
  assert (C : g x <-> f x x).
  { rewrite B. intuition. }
  unfold g in C.
  intuition.
Qed.
