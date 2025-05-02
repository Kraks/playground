Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.

Definition Assertion := state -> Prop.

Module ExAssertions.

Definition as1 : Assertion := fun st => st X = 3.

Definition as2 : Assertion := fun st => st X <= st Y.

Definition as3 : Assertion := fun st =>
  st X = 3 \/ st X <= st Y.

Definition as4 : Assertion := fun st =>
  st Z * st Z <= st X /\
  ~ (((S (st Z)) * (S (st Z))) <= st X).

Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                        (at level 80) : hoare_spec_scope.

(* Hoare Triples *)

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop := 
  forall st st',
    c / st \\ st' ->
    P st -> 
    Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{ P }} c {{ Q }}.
Proof.
  intros. unfold hoare_triple. intros.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple. intros.
  unfold not in H. apply H in H1.
  intuition.
Qed.

(* Proof Rules *)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (t_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{ Q [X |-> a] }} (X ::= a) {{ Q }}.
Proof.
  unfold assn_sub. unfold hoare_triple.
  intros. inversion H. subst.
  apply H0.
Qed.

(* strengthening the precondition, or
   weakening the postcondition also produce a
   valid Hoare triple *)

Theorem hoare_consequence_pre : forall P P' Q c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. unfold assert_implies.
  intros. eapply H.
  - apply H1.
  - apply H0. apply H2.
Qed.

Theorem hoare_consequence_post : forall P Q Q' c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. unfold  assert_implies.
  intros. apply H0. eapply H.
  - apply H1.
  - apply H2.
Qed.

Example hoare_asgn_example1 :
  {{ fun st => True }} 
  (X ::= (ANum 1))
  {{ fun st => st X = 1 }}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H. subst.
  unfold t_update. simpl.
  reflexivity.
Qed.

Theorem hoare_consequence : forall P P' Q Q' c,
  {{P'}} c {{Q'}} ->
  P ->> P' -> Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros. eapply hoare_consequence_pre.
  - eapply hoare_consequence_post.
    + apply H.
    + apply H1.
  - apply H0.
Qed.

(* Skip *)

Theorem hoare_skip : forall P,
  {{P}} SKIP {{P}}.
Proof.
  unfold hoare_triple.
  intros. inversion H. subst. apply H0.
Qed.

(* Sequence *)

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12. subst.
  eapply H1.
  - apply H6.
  - eapply H2.
    + apply H3.
    + apply Pre.
Qed.

Example hoare_asgn_example3 : forall a n,
  {{ fun st => aeval st a = n }}
  (X ::= a;; SKIP)
  {{ fun st => st X = n }}.
Proof.
  intros.
  eapply hoare_seq.
  - apply hoare_skip.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{ fun st => True }} 
  (X ::= (ANum 1);;
   Y ::= (ANum 2))
  {{ fun st => st X = 1 /\ st Y = 2 }}.
Proof.
  intros.
  eapply hoare_seq.
  - eapply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st H. unfold assn_sub.
      auto.
Qed.

(* TODO Exercises *)

(* Conditionals *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).
  
Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros. apply H.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ (bassn b) st.
Proof.
  unfold not. intros. inversion H0. 
  rewrite H2 in H. inversion H.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{ fun st => P st /\ bassn b st }} c1 {{ Q }} ->
  {{ fun st => P st /\ ~(bassn b st) }} c2 {{ Q }} ->
  {{ P }} (IFB b THEN c1 ELSE c2 FI) {{ Q }}.
Proof.
  intros. intros st st' HE HP.
  inversion HE; subst.
  - apply (H st st').
    + apply H7.
    + split. * apply HP. * apply H6.
  - apply (H0 st st').
    + apply H7.
    + split. * apply HP. * apply bexp_eval_false. intuition.
Qed.

Example if_example : 
  {{ fun st => True }}
  IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= (APlus (AId X) (ANum 1)))
  FI
  {{ fun st => st X <= st Y }}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold bassn, assn_sub, t_update, assert_implies.
      simpl. intros st [_ H]. apply beq_nat_true in H.
      omega.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assn_sub, t_update, assert_implies.
      simpl. intros st [_ H]. omega.
Qed.

(* TODO Exercises *)

(* Loops *)

Lemma hoare_while : forall P b c,
  {{ fun st => P st /\ bassn b st }} c {{ P }} ->
  {{ P }} WHILE b DO c END {{ fun st => P st /\ ~ (bassn b st) }}.
Proof.
  intros. intros st st' HE HP.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction HE; try (inversion Heqwcom); subst; clear Heqwcom.
  - split.
    + apply HP. + apply bexp_eval_false. apply H0.
  - apply IHHE2.
    + reflexivity.
    + eapply H.
      * apply HE1. * split. assumption. apply bexp_eval_true. apply H0.
Qed.

Example while_example : 
  {{ fun st => st X <= 3 }}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
  {{ fun st => st X = 3 }}.
Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold bassn, assn_sub, assert_implies, t_update.
      simpl. intros st [H1 H2]. apply leb_complete in H2.
      omega.
  - unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct (leb (st X) 2) eqn: Heqle.
    + destruct Hb. reflexivity.
    + apply leb_iff_conv in Heqle. omega.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{ P }} WHILE BTrue DO SKIP END {{ Q }}.
Proof.
  Admitted.