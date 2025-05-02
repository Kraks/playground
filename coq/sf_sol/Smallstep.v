Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Maps.
Require Import Imp.

(* A Toy Language *)

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '\\' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n, C n \\ n
  | E_Plus : forall t1 t2 n1 n2,
    t1 \\ n1 ->
    t2 \\ n2 ->
    P t1 t2 \\ (n1 + n2)
  where "t '\\' n" := (eval t n).

Module SimpleArith1.

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
    P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
    t1 ==> t1' ->
    P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
    t2 ==> t2' ->
    P (C n1) t2 ==> P (C n1) t2'
  where "t '==>' t'" := (step t t').

Example test_step_1 : 
  P (P (C 0) (C 3))
    (P (C 2) (C 4))
  ==>
  P (C (0 + 3))
    (P (C 2) (C 4)).
Proof.
  apply ST_Plus1.
  apply ST_PlusConstConst.
Qed.

Example test_step_2 :
  P (C 0)
    (P (C 2) (P (C 0) (C 3)))
  ==>
  P (C 0)
    (P (C 2) (C (0 + 3))).
Proof.
  apply ST_Plus2. apply ST_Plus2.
  apply ST_PlusConstConst.
Qed.

End SimpleArith1.

(* Relations *)

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic. intros.
  generalize dependent y2.
  induction H; intros.
  - inversion H0.
    + reflexivity.
    + subst. inversion H3.
    + subst. inversion H3.
  - inversion H0.
    + subst. inversion H.
    + rewrite <- (IHstep t1'0).
      * reflexivity.
      * apply H4.
    + rewrite <- H1 in H. inversion H.
  - inversion H0.
    + rewrite <- H3 in H. inversion H.
    + inversion H4.
    + rewrite <- (IHstep t2'0).
      * reflexivity.
      * apply H4.
Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with (S (S (?n'))) => subst; solve_by_inverts (S n') end]
  end end.

Ltac solve_by_invert := solve_by_inverts 1.

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt : deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros;
    inversion Hy2; subst; try solve_by_invert.
  - reflexivity.
  - apply IHHy1 in H2. rewrite H2. reflexivity.
  - apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

(* Values *)

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
    P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
    t1 ==> t1' ->
    P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    P v1 t2 ==> P v1 t2'
  where " t '==>' t' " := (step t t').

(* Exercise *)
Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros; inversion Hy2; subst; try solve_by_invert.
  - reflexivity.
  - apply IHHy1 in H2. rewrite H2. reflexivity.
  - inversion Hy2; subst.
    + inversion H1. subst. inversion Hy1.
    + inversion H1. subst. inversion Hy1.
  - inversion Hy2; subst.
    + inversion H. subst. try solve_by_invert.
    + inversion H. subst. try solve_by_invert.
  - apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.

(* Strong Progress and Normal Forms *)

(* Strong Progress: if t is a term, then either t is a value,
   or else there exists a term t' such that t ==> t' *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  intros. induction t.
  - left. apply v_const.
  - right. inversion IHt1.
    + inversion IHt2.
      * inversion H. inversion H0.
        exists (C (n + n0)). apply ST_PlusConstConst.
      * inversion H0.
        exists (P t1 x). apply ST_Plus2.
        apply H. apply H1.
    + inversion H. exists (P x t2). apply ST_Plus1.
      apply H0.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros.
  inversion H. intros contra.
  inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall v,
  normal_form step v -> value v.
Proof.
  unfold normal_form. intros.
  assert (G : value v \/ exists t', v ==> t').
  { apply strong_progress. }
  inversion G.
  - apply H0.
  - exfalso. apply H. apply H0.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  intros. split.
  apply nf_is_value.
  apply value_is_nf.
Qed.

(* TODO : Exercises *)

(* Multi-Step Reduction *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
    R x y ->
    multi R y z ->
    multi R x z.

Notation " t '==>*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> (multi R) x y.
Proof.
  intros.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans : forall (X : Type) (R : relation X) (x y z : X),
  multi R x y ->
  multi R y z ->
  multi R x z.
Proof.
  intros X R x y z Rxy Ryz.
  induction Rxy.
  - apply Ryz.
  - apply multi_step with y.
    apply H. apply IHRxy. apply Ryz.
Qed.

(* Examples *)

Lemma test_multistep_1 :
  P (P (C 0) (C 3))
    (P (C 2) (C 4))
  ==>*
  C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with (P (C (0 + 3)) (P (C 2) (C 4))).
  apply ST_Plus1. apply ST_PlusConstConst.
  apply multi_step with (P (C (0 + 3)) (C ( 2 + 4))).
  apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  apply multi_R.
  apply ST_PlusConstConst.
Qed.

(* Exercises TODO *)

(* Normal Forms Again *)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
      (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
  t1 ==>* t1' ->
  P t1 t2 ==>* P t1' t2.
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step with (P y t2).
    apply ST_Plus1. apply H.
    apply IHmulti.
Qed.

(* Exercise *)

Lemma multistep_congr_2 : forall t1 t2 t2',
  value t1 ->
  t2 ==>* t2' ->
  P t1 t2 ==>* P t1 t2'.
Proof.
  intros t1 t2 t2' Hvalt1 Ht2step.
  induction Ht2step.
  - apply multi_refl.
  - apply multi_step with (P t1 y).
    apply ST_Plus2.
    apply Hvalt1. apply H.
    apply IHHt2step.
Qed.

Theorem step_normalizing : normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - exists (C n). split.
    + apply multi_refl.
    + rewrite nf_same_as_value. apply v_const.
  - destruct IHt1 as [t1' [H11 H12]].
    destruct IHt2 as [t2' [H21 H22]].
    rewrite nf_same_as_value in H12.
    rewrite nf_same_as_value in H22.
    inversion H12 as [n1 H].
    inversion H22 as [n2 H'].
    rewrite <- H in H11.
    rewrite <- H' in H21.
    exists (C (n1 + n2)). split.
    + apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply H11.
      * apply multi_trans with (P (C n1) (C n2)).
        { apply multistep_congr_2. apply v_const. apply H21. }
        { apply multi_R. apply ST_PlusConstConst. }
    + rewrite nf_same_as_value. apply v_const.
Qed.

(* Equivalence of Big-Step and Small-Step *)

Theorem eval_multistep : forall t n,
  t \\ n -> t ==>* C n.
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - apply multi_trans with (P (C n1) t2).
    + apply multistep_congr_1. apply IHeval1.
    + apply multi_trans with (P (C n1) (C n2)).
      * apply multistep_congr_2. apply v_const. apply IHeval2.
      * apply multi_R. apply ST_PlusConstConst.
Qed.

(* Exercises *)

Lemma step_eval : forall t t' n,
  t ==> t' ->
  t' \\ n ->
  t \\ n.
Proof.
Admitted.

Theorem multistep_eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t \\ n.
Proof.
Admitted.

(* Small-Step Imp *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '-->a' t' "
         (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      (AId i) / st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMult a1 a2) / st -->a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMult v1 a2) / st -->a (AMult v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))
where " t '/' st '-->a' t' " := (astep st t t').

Reserved Notation " t '/' st '-->b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
  | BS_Eq1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (BEq a1 a2) / st -->b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (BEq v1 a2) / st -->b (BEq v1 a2')
  | BS_Eq : forall st n1 n2,
      (BEq (ANum n1) (ANum n2)) / st -->b
      (if (n1 =? n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (BLe a1 a2) / st -->b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (BLe v1 a2) / st -->b (BLe v1 a2')
  | BS_LtEq : forall st n1 n2,
      (BLe (ANum n1) (ANum n2)) / st -->b
              (if (n1 <=? n2) then BTrue else BFalse)
  | BS_NotStep : forall st b1 b1',
      b1 / st -->b b1' ->
      (BNot b1) / st -->b (BNot b1')
  | BS_NotTrue : forall st,
      (BNot BTrue) / st -->b BFalse
  | BS_NotFalse : forall st,
      (BNot BFalse) / st -->b BTrue
  | BS_AndTrueStep : forall st b2 b2',
      b2 / st -->b b2' ->
      (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
      b1 / st -->b b1' ->
      (BAnd b1 b2) / st -->b (BAnd b1' b2)
  | BS_AndTrueTrue : forall st,
      (BAnd BTrue BTrue) / st -->b BTrue
  | BS_AndTrueFalse : forall st,
      (BAnd BTrue BFalse) / st -->b BFalse
  | BS_AndFalse : forall st b2,
      (BAnd BFalse b2) / st -->b BFalse
where " t '/' st '-->b' t' " := (bstep st t t').

Reserved Notation " t '/' st '-->' t' '/' st' "
         (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st -->b b' ->
      IFB b THEN c1 ELSE c2 FI / st
      -->
      (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_While : forall st b c1,
      WHILE b DO c1 END / st
      -->
      (IFB b THEN c1;; WHILE b DO c1 END ELSE SKIP FI) / st
where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(* Concurrent Imp *)

(* A Small-Step Stack Machine *)

(* A normalize Tactic *)

Hint Constructors step value.

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
    ==>* (C 10).
Proof.
  eapply multi_step. eauto. simpl.
  eapply multi_step. eauto. simpl.
  constructor.
Qed.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step;
          [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Example step_example2 :
  (P (C 3) (P (C 3) (C 4)))
    ==>* (C 10).
Proof.
  normalize.
Qed.