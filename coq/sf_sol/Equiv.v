Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state), aeval st a1 = aeval st a2.
  
Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state), beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

Theorem skip_left : forall c,
  cequiv (SKIP;; c) c.
Proof.
  intros. unfold cequiv.
  split; intros.
  - inversion H. subst.
    inversion H2. subst.
    apply H5.
  - eapply E_Seq.
    + apply E_Skip.
    + apply H.
Qed.

Theorem skip_right : forall c,
  cequiv (c;; SKIP) c.
Proof.
  intros. unfold cequiv.
  split; intros.
  - inversion H. subst.
    inversion H5. subst.
    apply H2.
  - eapply E_Seq.
    + apply H.
    + apply E_Skip.
Qed.

Theorem IFB_true_simple : forall c1 c2,
  cequiv (IFB BTrue THEN c1 ELSE c2 FI) c1.
Proof.
  intros. unfold cequiv.
  split; intros.
  - inversion H. subst.
    + apply H6.
    + subst. inversion H5.
  - apply E_IfTrue.
    + reflexivity.
    + apply H.
Qed.

(* TODO Exercises *)

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv (WHILE b DO c END) SKIP.
Proof.
  unfold bequiv. unfold cequiv.
  intros. split; intros.
  - inversion H0; subst.
    * apply E_Skip.
    * rewrite H in H3. inversion H3.
  - inversion H0. subst.
    apply E_WhileFalse. rewrite H. reflexivity.
Qed.

(* TODO Exercises *)

Theorem loop_unrolling : forall b c,
  cequiv 
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  unfold cequiv. intros. split; intros.
  - inversion H; subst.
    + apply E_IfFalse.
      * apply H4.
      * apply E_Skip.
    + apply E_IfTrue.
      * apply H2.
      * eapply E_Seq.
        apply H3.
        apply H6.
  - inversion H; subst.
    + inversion H6. subst. eapply E_WhileTrue.
      apply H5. apply H2. apply H7.
    + inversion H6. subst. apply E_WhileFalse. assumption.
Qed.

Theorem identity_assignment : forall (X : id),
  cequiv (X ::= AId X) SKIP.
Proof.
  unfold cequiv. intros. split; intros.
  - inversion H. subst.
    simpl. replace (t_update st X (st X)) with st.
    + apply E_Skip.
    + apply functional_extensionality. intros. rewrite t_update_same.
      reflexivity.
  - replace st' with (t_update st' X (aeval st' (AId X))).
    + inversion H. subst. apply E_Ass.
      reflexivity.
    + apply functional_extensionality.
      intros. rewrite t_update_same. reflexivity.
Qed.

(* Properties of Behavioral Equivalence *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros. unfold aequiv. intros. reflexivity.
Qed.

(* TODO ... *)

(* Behavioral Equivalence is a Congruence *)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  unfold aequiv. unfold cequiv.
  intros. split; intros.
  - inversion H0. subst. apply E_Ass. 
    rewrite H. reflexivity.
  - inversion H0. subst. apply E_Ass.
    rewrite H. reflexivity.
Qed.

(* TODO congruence of other language constructors *)