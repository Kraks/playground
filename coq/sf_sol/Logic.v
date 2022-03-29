Require Export Tactics.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
Qed.

Check @eq.

(* Conjunction *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  reflexivity. reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  apply HA. apply HB.
Qed.

(* Exercises *)

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m.
  destruct n.
  - intros H.
    split.
    + reflexivity.
    + apply H.
  - intros H.
    split. 
    inversion H.
    inversion H.
Qed.

(* use a conjunctive hypothesis to prove something *)

Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 : forall n m,
  n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert ( H' : n = 0 /\ m = 0 ).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn.
  reflexivity.
Qed.

(* Exercise *)

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split. apply HQ. apply HP.
Qed.

(* Exercise *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP HQR].
  destruct HQR as [HQ HR].
  split. split.
  apply HP.
  apply HQ.
  apply HR.
Qed.

Check and.

(* Disjunction *)

Lemma or_example : forall n m,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ : forall n, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Exercise *)

Lemma mult_eq_0 : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n.
  - left. reflexivity.
  - right. destruct m.
    + reflexivity.
    + inversion H.
Qed.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(* Falsehood and Negation *)

Module MyNot.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(* Exercise *)

Fact not_implies_out_not : forall P : Prop,
  ~ P -> (forall Q : Prop, P -> Q).
Proof.
  intros P NP Q HP.
  destruct NP.
  apply HP.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra.
  inversion contra.
Qed.

Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem not_False : ~ False.
Proof.
  unfold not.
  intros H. 
  destruct H.
Qed.

Theorem contradition_implies_anything : forall P Q : Prop, 
  (P /\ ~ P) -> Q.
Proof.
  intros P Q H.
  destruct H.
  unfold not in H0.
  apply H0 in H.
  inversion H.
Qed.

Theorem double_neg : forall P : Prop, P -> ~~ P.
Proof.
  intros P H.
  unfold not.
  intros H0.
  apply H0 in H.
  inversion H.
Qed.

(* Exercise *)

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~ Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros H0 H1.
  apply H0 in H.
  - inversion H.
  - apply H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  destruct H.
  apply H0 in H.
  inversion H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

(* Truth *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(* Logical Equivalence *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB.
Qed.

Theorem not_true_iff_false : forall b, 
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H.
    rewrite H.
    intros H'.
    inversion H'.
Qed.

(* Exercise *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  - intros H. apply H.
  - intros H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros [HPQ HQP] [HQR HRQ].
  split.
  - intros H. apply HQR. apply HPQ. apply H.
  - intros H. apply HQP. apply HRQ. apply H.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ HR]].
    + split. left. apply HP.
             left. apply HP.
    + split. right. apply HQ.
             right. apply HR.
  - intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP2.
    + left. apply HP1.
    + left. apply HP2.
    + right. split. apply HQ. apply HR.
Qed.


Require Import Coq.Setoids.Setoid.

Check mult_eq_0.
Check or_example.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc : forall P Q R: Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 : forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  apply mult_0.
  apply H.
Qed.

(* Existential Quantification *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m EM].
  exists (2 + m).
  apply EM.
Qed.

(* Exercises *)

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H E.
  inversion E.
  apply H0. apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.

(* Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
match l with
  | nil => False
  | cons x' xs => x' = x \/ In x xs
end.

Example In_example_1 : In 4 [1; 4; 2; 3; 5].
Proof.
  simpl.
  right. left. reflexivity.
Qed.

Example In_example_2 : 
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H2 | [H4 | []]].
  - exists 1. rewrite <- H2. reflexivity.
  - exists 2. rewrite <- H4. reflexivity.
Qed.

Lemma In_map : 
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B F l x.
  induction l as [|x' xs H].
  - simpl. intros [].
  - simpl. intros [H' | H'].
    + rewrite H'. left. reflexivity.
    + right. apply H. apply H'.
Qed.

(* Exercise *)

Lemma In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - generalize l y. induction l0.
    + intros y0. simpl. intros contra. inversion contra.
    + intros y0. simpl. intros [H | H].
      * exists x. split. apply H. left. reflexivity.
      * apply IHl0 in H. destruct H. exists x0.
        destruct H as [H1 H2].
        split. apply H1. right. apply H2.
  - intros H. induction l.
    + simpl. destruct H. inversion H. inversion H1.
    + simpl. destruct H. destruct H as [H1 H2].
      simpl in H2. destruct H2 as [HEQ | HNEQ].
      * left. rewrite <- H1. rewrite HEQ. reflexivity.
      * right. apply IHl. exists x0. split.
        apply H1. apply HNEQ.
Qed.

Lemma in_app_iff : forall A l l' (a : A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  Admitted.

(* TODO: Exercises *)

(* TODO: Applying Theorems to Arguments *)

(* TODO: Coq vs Set Theory *)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  split.
  - intros. destruct b1.
    + destruct b2.
      * split. reflexivity. reflexivity.
      * split. reflexivity. inversion H.
    + destruct b2.
      * split. inversion H. reflexivity.
      * split. inversion H. inversion H.
  - intros. destruct b1.
    + destruct b2.
      * reflexivity.
      * inversion H. inversion H1.
    + destruct b2.
      * inversion H. inversion H0.
      * inversion H. inversion H1.
Qed.

Lemma orb_true_iff : forall b1 b2 : bool,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof. Admitted.
