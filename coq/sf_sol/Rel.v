Set Warnings "-notation-overridden, -parsing".
Require Export IndProp.

(* Relations *)

Definition relation (X : Type) := X -> X -> Prop.

(* Partial Relations *)

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros. inversion H. inversion H0.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold partial_function. unfold not.
  intros Hc.
  assert (0 = 1) as Nonsense.
  { apply Hc with (x := 0).
    - apply le_n. - apply le_S. apply le_n. }
  inversion Nonsense.
Qed.

(* Reflexive Relations *)

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Theorem le_refleixive : reflexive le.
Proof.
  unfold reflexive. intros.
  apply le_n.
Qed.

(* Transitive Relations *)

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans : transitive le.
Proof.
  unfold transitive. intros.
  induction H0.
  - apply H.
  - apply le_S. apply IHle.
Qed.

(* TODO: Exercises *)

(* Symmetric and Antisymmetric Relations *)

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric : ~ (symmetric le).
Proof.
  unfold not. unfold symmetric.
  intros. assert (4 <= 3).
  { apply H. apply le_S. reflexivity. }
  intuition.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric.
  intros. inversion H.
  - reflexivity.
  - intuition.
Qed.

Theorem le_step : forall n m p, n < m -> m <= S p -> n <= p.
Proof.
  Admitted.

(* Equivalence Relations *)

Definition equivalence {X : Type} (R : relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order : order le.
Proof.
  unfold order.
  split.
  - apply le_refleixive.
  - split. + apply le_antisymmetric. + apply le_trans.
Qed.

(* Reflexive, Transitive Closure *)

(* The reflexive, transitive closure of a relation R is the
   smallest relation that contains R and that is both reflexive
   and transitive. *)

Inductive clos_refl_trans {A : Type} (R : relation A) : relation A :=
  | rt_step : forall x y, R x y -> clos_refl_trans R x y
  | rt_refl : forall x, clos_refl_trans R x x
  | rt_trans : forall x y z,
    clos_refl_trans R x y ->
    clos_refl_trans R y z ->
    clos_refl_trans R x z.

(* TODO *)
