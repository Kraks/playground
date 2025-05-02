(* https://people.cs.uchicago.edu/~caldwellb/vqc/toc.html *)

(* Axiomatizing Real *)

Module OurR.

Parameter R : Set.
Delimit Scope R_scope with R.
Local Open Scope R_scope.

Parameter R0 : R.
Parameter R1 : R.

Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.
Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

Definition Rminus (r1 r2:R) : R := r1 + - r2.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.
Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv : R_scope.

Fixpoint INR (n : nat) : R :=
  match n with
  | O => R0
  | 1 => R1
  | S n' => R1 + INR n'
  end.

Coercion INR : nat >-> R.
Check 4 + 5.
Compute (4 + 5).

(* Field *)

Axiom R1_neq_R0 : INR 1 <> INR 0.
Axiom Rplus_comm : forall r1 r2 : R, r1 + r2 = r2 + r1.
Axiom Rplus_assoc : forall r1 r2 r3 : R, r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Rplus_opp_r : forall r : R, r + -r = 0.
Axiom Rplus_0_l : forall r : R, 0 + r = r.

Lemma Rplus_0_r : forall r : R, r + 0 = r.
Proof.
  intros. rewrite Rplus_comm. apply Rplus_0_l.
Qed.

Lemma Rplus_opp_l : forall r, -r + r = 0.
Proof.
  intros. rewrite Rplus_comm. apply Rplus_opp_r.
Qed.

Lemma Ropp_0 : -0 = 0.
Proof.
  rewrite <- (Rplus_0_l (-0)). rewrite Rplus_opp_r. auto.
Qed.

Lemma Rplus_cancel_l : forall r1 r2 r3, r1 + r2 = r1 + r3 -> r2 = r3.
Proof.
  intros.
  rewrite <- Rplus_0_l. rewrite <- (Rplus_opp_l r1). rewrite Rplus_assoc.
  rewrite <- H. rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l. auto.
Qed.

Lemma R0_unique : forall r1 r2, r1 + r2 = r1 -> r2 = 0.
Proof.
  intros r1 r2 H. rewrite <- Rplus_0_r in H. eapply Rplus_cancel_l. apply H.
Qed.

Axiom Rmult_comm : forall r1 r2 : R, r1 * r2 = r2 * r1.
Axiom Rmult_assoc : forall r1 r2 r3, r1 * r2 * r3 = r1 * (r2 * r3).
Axiom Rinv_l : forall r : R, r <> 0 -> / r * r = 1.
Axiom Rmult_1_l : forall r : R, 1 * r = r.
Axiom Rmult_plus_distr_l : forall r1 r2 r3 : R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.

Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  intros r. apply (R0_unique (r * 0)). rewrite <- Rmult_plus_distr_l. rewrite Rplus_0_l. auto.
Qed.

Lemma Rmult_plus_distr_r : forall r1 r2 r3 : R, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros. rewrite Rmult_comm. rewrite Rmult_plus_distr_l. rewrite 2 (Rmult_comm r3). auto.
Qed.

Lemma Rinv_r : forall r : R, r <> 0 -> r * / r = 1.
Proof.
  intros. rewrite Rmult_comm. apply Rinv_l. auto.
Qed.

(* ring and field tactics *)

Require Export Ring.
Require Export Field.

Lemma R_Ring_Theory : ring_theory R0 R1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  apply Rplus_0_l.
  apply Rplus_comm.
  intros. rewrite Rplus_assoc. auto.
  apply Rmult_1_l.
  apply Rmult_comm.
  intros. rewrite Rmult_assoc. auto.
  apply Rmult_plus_distr_r.
  auto.
  apply Rplus_opp_r.
Defined.

Add Ring RRing : R_Ring_Theory.

Lemma R_Field_Theory : field_theory R0 R1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof.
  constructor.
  apply R_Ring_Theory.
  apply R1_neq_R0.
  auto.
  apply Rinv_l.
Defined.

Add Field RField : R_Field_Theory.

Example ring_test1 : forall x : R, x + x = 2 * x.
Proof.
  intros. simpl. ring.
Qed.

Example ring_test2 : forall x y z: R, x * y + z = z + y * x.
Proof.
  intros. ring.
Qed.

Example field_test1 : forall x y : R, x <> 0 -> x * y / x = y.
Proof.
  intros. field. auto.
Qed.

(* Ordering *)

Parameter Rlt : R -> R -> Prop.

Infix "<" := Rlt : R_scope.

Definition Rgt (r1 r2 : R) : Prop := r2 < r1.
Definition Rle (r1 r2 : R) : Prop := r1 < r2 \/ r1 = r2.
Definition Rge (r1 r2 : R) : Prop := Rgt r1 r2 \/ r1 = r2.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">" := Rgt : R_scope.
                                                  
Axiom total_order_T : forall r1 r2 : R, {r1 < r2} + {r1 = r2} + {r1 > r2}.
Axiom Rlt_asym : forall r1 r2 : R, r1 < r2 -> ~ (r2 < r1).
Axiom Rlt_trans : forall r1 r2 r3 : R, r1 < r2 -> r2 < r3 -> r1 < r3.
Axiom Rplus_lt_compact_l : forall r r1 r2 : R, r1 < r2 -> r + r1 < r + r2.
Axiom Rmult_lt_compact_l : forall r r1 r2 : R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

(* Completeness:
   every bounded subset of real numbers has a least upper bound, which is a real number.
*)

Definition is_upper_bound (E : R -> Prop) (m : R) := forall x : R, E x -> x <= m.

Definition bound (E : R -> Prop) := exists m : R, is_upper_bound E m.

Definition is_lub (E : R -> Prop) (m : R) :=
  is_upper_bound E m /\ (forall b : R, is_upper_bound E b -> m <= b).

Axiom completeness : forall (E : R -> Prop), bound E -> (exists x : R, E x) -> { m : R | is_lub E m }.
Axiom completeness' : forall (E : R -> Prop), bound E -> (exists x : R, E x) -> (sig (A:=R) (fun m => is_lub E m)).

(* Defining irrational numbers *)

Lemma Rlt_0_1 : 0 < 1. Admitted.

Definition lt_sqrt2 (x : R) := x * x < 2.

Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2. simpl.
  intros. left.
  destruct (total_order_T x 1) as [[L | E] | G].
  - rewrite <- (Rplus_0_r x).
    eapply Rlt_trans. apply Rplus_lt_compact_l.
    apply Rlt_0_1. rewrite Rplus_comm. apply Rplus_lt_compact_l. auto.
  - rewrite E. rewrite <- (Rplus_0_r 1). apply Rplus_lt_compact_l.
    apply Rlt_0_1.
  - assert (x * 1 < x * x). apply Rmult_lt_compact_l. eapply Rlt_trans.
    apply Rlt_0_1. apply G. apply G. rewrite Rmult_comm, Rmult_1_l in H0.
    eapply Rlt_trans. apply H0. apply H.
Qed.

Lemma bound_sqrt2 : bound lt_sqrt2.
Proof. exists 2. apply upper_bound_2_sqrt_2. Qed.

Lemma ex_lt_sqrt2 : exists x, lt_sqrt2 x.
Proof.
  exists 1. unfold lt_sqrt2. rewrite Rmult_1_l.
  rewrite <- (Rplus_0_r 1); simpl. apply Rplus_lt_compact_l.
  apply Rlt_0_1.
Qed.

Definition sqrt2 := completeness lt_sqrt2 bound_sqrt2 ex_lt_sqrt2.

End OurR.
