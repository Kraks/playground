(* Basics *)

(* Days of week *)
Inductive day : Type := 
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday :
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(*
* The assertion we've just made can be proved by observing 
* that both sides of the equality evaluate to the same thing, 
* after some simplification.
*)

(* Booleans *)
Inductive bool : Type :=
  | true : bool 
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Exercise: nandb *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (b1 && b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: andb3 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (andb (andb b1 b2) b3).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Function Types *)

Check true.

Check (negb true).

Check negb.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n:nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 2 = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat := 
match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(* Exercise: factorial *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult (S n') (fact n')
  end.

Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Check ((0+1)+1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.
Check leb.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: blt_nat *)
Definition blt_nat (n m : nat) : bool :=
  (leb n m) && (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Proof by Simplification *)
(* use simpl to simplify both sides of the equation, then use reflexivity to check that both sides contain identical values. *)

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.

(* Proof by Rewriting *)
Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  (* move both the quantifiers into the context *)
  intros n m.
  (* move the hypothesis into the context *)
  intros H.
  (* rewrite the goal using the hypothesis *)
  rewrite -> H.
  reflexivity. 
Qed.

(*
The first line of the proof moves the universally quantified variables n and m into the context. 
The second moves the hypothesis n = m into the context and gives it the name H. 
The third tells Coq to rewrite the current goal (n + n = m + m) by replacing the left side of the equality hypothesis H with the right side. 
*)

(* Exercise 1*)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. 
Qed.

(* Exercise 2*)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. 
Qed.

(* Proof by Case Analysis *)
Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity. 
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(* Exercise *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
    - reflexivity. 
    - rewrite <- H.
      destruct b.
      + reflexivity. 
      + reflexivity.
Qed.

(*
It tells Coq what variable names to introduce in each subgoal. In general, what goes between the square brackets is a list of lists of names, separated by |. In this case, the first component is empty, since the O constructor is nullary (it doesn't have any arguments). The second component gives a single name, n', since S is a unary constructor.  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n']. (* intro pattern *)
  - reflexivity.
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H.
  destruct b.
  - rewrite H. rewrite H. reflexivity.
  - rewrite H. rewrite H. reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H.
  destruct b.
  - rewrite H. rewrite H. reflexivity.
  - rewrite H. rewrite H. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  unfold andb.
  intros H.
  destruct b.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Inductive bin : Type :=
| Zero : bin
| TwiceOf : bin -> bin
| OneMoreTwiceOf : bin-> bin.

Fixpoint incr (b : bin) : bin :=
match b with
| Zero => OneMoreTwiceOf Zero
| TwiceOf b' => OneMoreTwiceOf b'
| OneMoreTwiceOf b' => TwiceOf (incr b')
end.

(* 
0 => Zero
1 => OneMoreTwiceOf Zero
10 => TwiceOf (OneMoreTwiceOf Zero)
11 => OneMoreTwiceOf (OneMoreTwiceOf Zero)
*)

Fixpoint bin_to_nat (b : bin) : nat :=
match b with
| Zero => O
| TwiceOf b' => 2 * (bin_to_nat b')
| OneMoreTwiceOf b' => 1 + 2 * (bin_to_nat b')
end.

Example test_bin_incr1 : (bin_to_nat Zero) = 0.
Proof. reflexivity. Qed.
Example test_bin_incr2 : (bin_to_nat (incr Zero)) = 1.
Proof. reflexivity. Qed.
Example test_bin_incr3 : (bin_to_nat (incr (incr Zero))) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr4 : (bin_to_nat (incr (incr (incr Zero)))) = 3.
Proof. reflexivity. Qed.
Example test_bin_incr5 : (bin_to_nat (incr (incr (incr (incr Zero))))) = 4.
Proof. reflexivity. Qed.
