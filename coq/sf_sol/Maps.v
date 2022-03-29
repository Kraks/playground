From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(* Identifiers *)

Inductive id : Type :=
  | Id : string -> id.

Definition beq_id x y :=
  match x, y with
  | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. destruct (string_dec n n).
  - reflexivity.
  - destruct n0. reflexivity.
Qed.

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
  intros [n1] [n2]. unfold beq_id.
  destruct (string_dec n1 n2).
  - split. 
    + intros. rewrite e. reflexivity.
    + intros. reflexivity.
  - split.
    + intros. inversion H.
    + intros. inversion H. subst. intuition.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false <-> x <> y.
Proof.
  intros [n1] [n2]. unfold beq_id.
  destruct (string_dec n1 n2).
  - split. 
    + intros. inversion H.
    + intros. rewrite e in H. intuition.
  - split.
    + intros. intuition. apply n. inversion H0. reflexivity.
    + intros. reflexivity.
Qed.

Theorem false_beq_id : forall x y : id,
  x <> y -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros. apply H.
Qed.

(* Total Maps *)

Definition total_map (A : Type) := id -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) (Id "foo") false)
           (Id "bar") true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( (Id "bar") !-> true;
    (Id "foo") !-> true;
    _ !-> false
  ).

(* Exercises *)

Lemma t_apply_empty: forall A x v, @t_empty A v x = v.
Proof.
  intros.
  unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall A (m : total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros.
  unfold t_update.
  destruct (beq_id x x) eqn: eqxx.
  - reflexivity.
  - apply beq_id_false_iff in eqxx. intuition.
Qed.

Lemma t_update_neq : forall X v x1 x2 (m : total_map X),
  x1 <> x2 -> (t_update m x1 v) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  destruct (beq_id x1 x2) eqn: eqx1x2.
  - apply beq_id_true_iff in eqx1x2. intuition.
  - reflexivity.
Qed.

Lemma t_update_shadow : forall A (m : total_map A) v1 v2 x,
  t_update (t_update m x v1) x v2 = t_update m x v2.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality. intros.
  destruct (beq_id x x0) eqn: H.
  - reflexivity.
  - reflexivity.
Qed.

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros.
  destruct (beq_id x y) eqn: H.
  - apply ReflectT. apply beq_id_true_iff. apply H.
  - apply ReflectF. apply beq_id_false_iff. apply H.
Qed.

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros. 
  unfold t_update.
  apply functional_extensionality. intros.
  destruct (beq_id x x0) eqn: H.
  - apply f_equal. apply beq_id_true_iff in H. apply H.
  - reflexivity.
Qed.

Theorem t_update_permute : forall X v1 v2 x1 x2 (m : total_map X),
  x2 <> x1 -> (t_update (t_update m x2 v2) x1 v1)
            = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros. unfold t_update.
  apply functional_extensionality. intros.
  destruct (beq_id x1 x) eqn: Hx1x;
  destruct (beq_id x2 x) eqn: Hx2x.
  - apply beq_id_true_iff in Hx1x.
    apply beq_id_true_iff in Hx2x.
    rewrite <- Hx1x in Hx2x. destruct H. apply Hx2x.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Partial Maps *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.
  
Definition update {A : Type} (m : partial_map A) (x : id) (v : A) :=
  t_update m x (Some v).

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. unfold t_empty. reflexivity.
Qed.

Lemma update_eq : forall A (m : partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. unfold t_update.
  destruct (beq_id x x) eqn: H.
  - reflexivity.
  - apply beq_id_false_iff in H. intuition.
Qed.

Lemma update_neq : forall X v x1 x2 (m : partial_map X),
  x2 <> x1 -> (update m x2 v) x1 = m x1.
Proof.
  intros. unfold update. unfold t_update.
  destruct (beq_id x2 x1) eqn: eqx2x1.
  - apply beq_id_true_iff in eqx2x1. intuition.
  - reflexivity.
Qed.

Lemma update_shadow : forall A (m : partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros. unfold update. unfold t_update.
  apply functional_extensionality. intros.
  destruct (beq_id x x0) eqn: H.
  - reflexivity.
  - reflexivity.
Qed.

Lemma update_same : forall X v x (m : partial_map X),
  m x = Some v -> update m x v = m.
Proof.
  intros. unfold update. unfold t_update.
  apply functional_extensionality. intros.
  destruct (beq_id x x0) eqn: eqxx0.
  - apply beq_id_true_iff in eqxx0. rewrite <- eqxx0.
    intuition.
  - reflexivity.
Qed.

Theorem update_permute : forall (X : Type) v1 v2 x1 x2 (m : partial_map X),
  x2 <> x1 -> (update (update m x2 v2) x1 v1)
            = (update (update m x1 v1) x2 v2).
Proof.
  intros. unfold update. apply t_update_permute.
  apply H.
Qed.
