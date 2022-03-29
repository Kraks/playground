Require Export Basics.

Theorem plus_n_0 : forall n : nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity. (* n = 0 *)
  - simpl. rewrite <- IHn'. reflexivity. (* n = S n' *)
Qed.

Theorem minus_diag : forall n : nat,
  minus n n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercise *)
Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m: nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite <- plus_n_0. simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Fixpoint double (n : nat) := 
  match n with
  | O => O
  | S n' => S(S(double n'))
end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  unfold double.
  induction n as [| n'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> plus_n_Sm. reflexivity.
Qed.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | (S O) => false
  | (S (S n')) => evenb n'
  end.
  
Theorem nnb : forall b : bool, negb (negb b) = b.
Proof.
  intros b.
  induction b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  intros n.
  unfold evenb.
  induction n as [| n'].
  - simpl. reflexivity.
  - rewrite -> IHn'. rewrite -> nnb. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : n + m = m + n). {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H : p + n = n + p). { rewrite -> plus_comm. reflexivity. }
  rewrite <- plus_comm.
  rewrite <- H.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_n_Sm : forall m n : nat,
  n * S m = n + n * m.
Proof.
  intros m n.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_swap. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [| m'].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite -> IHm'. rewrite mult_n_Sm. reflexivity.
Qed.

(* first think about whether 
     (a) it can be proved using only simplification and rewriting, 
     (b) it also requires case analysis (destruct), or 
     (c) it also requires induction.
*)

Theorem leb_refl : forall n : nat,
  true = leb n n.
Proof.
  intros n.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [| p'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.

Theorem Sn_beq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n.
  simpl. 
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb (andb b c)
      (orb (negb b) (negb c))
      = true.
Proof.
  intros b c.
  destruct b.
  - simpl.
    destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_comm.
  replace (n + p) with (p + n).
  - rewrite plus_assoc. reflexivity.
  - rewrite plus_comm. reflexivity.
Qed.

(* TODO: bin_to_nat_pres_incr *)

(* TODO: binary_inverse *)
