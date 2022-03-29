(* Tactics *)

Require Export Poly.

(* The apply Tactic *)

(* when we use apply H, the statement H will begin 
   with a ∀ that binds some universal variables. 
   When Coq matches the current goal against the 
   conclusion of H, it will try to find appropriate 
   values for these variables. *)

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true ->
      oddb 4 = true.
Proof.
  intros n.
  apply n.
Qed.

Theorem silly3 : forall n : nat,
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  symmetry.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite H. symmetry. apply rev_involutive.
Qed.

(* The apply ... with ... Tactics *)

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o H1 H2.
  rewrite H1. rewrite H2.
  reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  apply trans_eq with (m := [c;d]).
  apply H1.
  apply H2.
Qed.

Example trans_eq_exercise : forall (n m o p: nat),
   m = (minustwo o) ->
   (n + p) = m ->
   (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  apply trans_eq with (m := m).
  apply H2. apply H1.
Qed.

(* The inversion Tactic *)

(* The constructor S is injective. 
   That is, if S n = S m, it must be the case that n = m. *)
(* The constructors O and S are disjoint. 
   That is, O is not equal to S n for any n. *)

Theorem S_injective : forall n m : nat,
  S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : forall n m o : nat,
  [n;m] = [o;o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall n m : nat,
  [n] = [m] -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity. 
Qed.

Theorem inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H2.
  reflexivity.
Qed.

Theorem beq_nat_0_1 : forall n, beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - intros H. reflexivity.
  - simpl. intros H. inversion H.
Qed.

(* principle of explosion, which asserts that a contradictory 
   hypothesis entails anything, even false things. *)

Theorem inversion_ex4 : forall n : nat,
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem inversion_ex5 : forall n m : nat,
  false = true -> [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

Example inversion_ex6 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j -> 
  x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

(* Using Tactics on Hypotheses *)

Theorem S_inj : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

(* apply L in  H is forward reasoning: from L1 -> L2 and 
   a hypothesis matching L1, it produces a hypothesis matching L2. *)

(* apply L is backward reasoning, it says that if we know L1 -> l2,
   we are trying to prove L2, it suffices to prove L1. *)

Theorem silly3' : forall n : nat,
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - intros m H. destruct m.
    reflexivity.
    inversion H.
  - intros m. destruct m.
    + intros H. inversion H.
    + intros H. inversion H.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1. apply IHn' in H2.
      rewrite -> H2. reflexivity.
Qed.

(* Varying the Induction Hypothesis *)

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n.
  induction n.
  - simpl. intros m eq.
    destruct m.
    + reflexivity.
    + inversion eq.
  - simpl.
    intros m eq.
    destruct m.
    + inversion eq.
    + apply f_equal. apply IHn. inversion eq. reflexivity.
Qed.

(* Exercises *)

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros m eq. destruct m.
    + reflexivity.
    + inversion eq.
  - intros m eq.
    destruct m.
    + inversion eq.
    + apply f_equal. apply IHn. apply eq.
Qed.

Theorem double_injective_2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - simpl. intros n eq. destruct n as [| n'].
    + reflexivity.
    + inversion eq.
  - intros n eq. destruct n as [| n'].
    + inversion eq.
    + apply f_equal. apply IHm'. inversion eq. reflexivity.
Qed.

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(* Exercises *)

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l.
  - intros n eq.
    destruct n.
    + reflexivity.
    + simpl. reflexivity.
  - intros n eq.
    destruct n.
    + simpl. inversion eq.
    + simpl. apply IHl. inversion eq. reflexivity.
Qed.

(* Unfolding Definitions *)

Definition square n := n * n.

Lemma square_mult : forall n m, 
  square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc.
  reflexivity.
Qed.

(* Using destruct on Compound Expressions *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall n : nat,
  sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  - reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity.
Qed.

(* Exercises *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - simpl. intros l1 l2 H. inversion H. reflexivity.
  - intros l1 l2.
    destruct x. simpl.
    intros H. inversion H.
    assert (L : forall a b, a = b -> (x,y)::a = (x,y)::b).
    { intros a b LH. rewrite LH. reflexivity. }
    apply L. apply IHl.
    assert (eq_pair : forall A B (z : A*B), z = (fst z, snd z)).
    { intros A B z. destruct z. reflexivity. }
    apply eq_pair.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd : forall n : nat,
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  - apply beq_nat_true in Heqe3.
    rewrite -> Heqe3.
    reflexivity.
  - destruct (beq_nat n 5) eqn:Heqe5.
    + apply beq_nat_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + inversion eq.
Qed.

(* Exercise *)

Theorem bool_fn_applied_thrice:
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - destruct (f true) eqn:ft.
    + rewrite ft. apply ft.
    + destruct (f false) eqn:ff.
      * apply ft.
      * apply ff.
  - destruct (f false) eqn:ff.
    + destruct (f true) eqn:ft.
      * apply ft.
      * apply ff.
    + rewrite ff. apply ff.
Qed.

(* Review *)

(*
intros: move hypotheses/variables from goal to context

reflexivity: finish the proof (when the goal looks like e = e)

apply: prove goal using a hypothesis, lemma, or constructor

apply... in H: apply a hypothesis, lemma, or constructor to a 
               hypothesis in the context (forward reasoning)

apply... with...: explicitly specify values for variables that 
                  cannot be determined by pattern matching

simpl: simplify computations in the goal

simpl in H: ... or a hypothesis

rewrite: use an equality hypothesis (or lemma) to rewrite the goal

rewrite ... in H: ... or a hypothesis

symmetry: changes a goal of the form t=u into u=t

symmetry in H: changes a hypothesis of the form t=u into u=t

unfold: replace a defined constant by its right-hand side in the goal

unfold... in H: ... or a hypothesis

destruct... as...: case analysis on values of inductively defined types

destruct... eqn:...: specify the name of an equation to be added to 
                     the context, recording the result of the case analysis
                     
induction... as...: induction on values of inductively defined types

inversion: reason by injectivity and distinctness of constructors

assert (H: e) (or assert (e) as H): introduce a "local lemma" e and call it H

generalize dependent x: move the variable x (and anything else that depends on it)
                        from the context back to an explicit hypothesis in the goal formula
*)

(* Additional Excercises *)

Theorem beq_nat_sym : forall n m : nat,
  beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n.
  - destruct m.
    + reflexivity.
    + unfold beq_nat. reflexivity.
  - intros m.
    destruct m.
    + reflexivity.
    + apply IHn.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_true in eq1.
  apply beq_nat_true in eq2.
  rewrite eq1. rewrite eq2.
  symmetry. apply beq_nat_refl.
Qed.

Definition split_combine_stmt : Prop :=
  forall X Y (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_stmt.
Proof.
  intros X Y l1.
  induction l1.
  - intros l2 H. destruct l2.
    + reflexivity.
    + inversion H.
  - intros l2 H.
    inversion H.
    simpl.
    destruct l2.
    + inversion H.
    + inversion H.
      apply IHl1 in H2.
      simpl.
      destruct (split (combine l1 l2)).
      simpl. inversion H2. reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
  (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l lf.
  induction l.
  - simpl. intros H. inversion H.
  - simpl. intros H. destruct (test x0) eqn:eq0.
    + inversion H. rewrite <- H1. apply eq0.
    + apply IHl in H. apply H.
Qed.

(* TODO: Exercise: 4 stars, advanced, recommended (forall_exists_challenge) *)

