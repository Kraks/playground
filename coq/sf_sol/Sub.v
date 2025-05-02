Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import NewMaps.
Require Import Types.
Require Import Smallstep.
From Coq Require Import Nat.

(* Formal Definitions *)

(* Syntax *)

Inductive ty : Type :=
  | Top : ty
  | Bool : ty
  | Unit : ty
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
.

Notation "t1 '⇒' t2" := (Arrow t1 t2) (at level 40).

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | unit : tm
.

(* substitution *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var y =>
    if eqb_string x y then s else t
  | abs y T t1 =>
    abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
    app (subst x s t1) (subst x s t2)
  | tru => tru
  | fls => fls
  | unit => unit
  | test t1 t2 t3 =>
    test (subst x s t1) (subst x s t2) (subst x s t3)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_true : value tru
  | v_false : value fls
  | v_unit : value unit
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      value v2 ->
      (app (abs x T t12) v2) --> [x := v2] t12
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      (app v1 t2) --> (app v1 t2')
  | ST_TestTrue : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFalse : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(* Subtyping *)

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T, T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S, S <: Top
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      (Arrow S1 S2) <: (Arrow T1 T2)
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.

Module Examples.
  Open Scope string_scope.

  Notation x := "x".
  Notation y := "y".
  Notation z := "z".
  Notation A := (Base "A").
  Notation B := (Base "B").
  Notation C := (Base "C").

  Notation String := (Base "String").
  Notation Float := (Base "Float").
  Notation Integer := (Base "Integer").

  Example subtyping_ex_0 :
    (Arrow C Bool) <: (Arrow C Top).
  Proof.
    auto.
  Qed.
End Examples.

(* Typing *)

Definition context := partial_map ty.

Reserved Notation "Γ '⊢' t '∈' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Γ x T,
      Γ x = Some T ->
      Γ ⊢ var x ∈ T
  | T_Abs : forall Γ x T11 T12 t12,
      (x |-> T11 ; Γ) ⊢ t12 ∈ T12 ->
      Γ ⊢ abs x T11 t12 ∈ Arrow T11 T12
  | T_App : forall Γ T1 T2 t1 t2,
      Γ ⊢ t1 ∈ Arrow T1 T2 ->
      Γ ⊢ t2 ∈ T1 ->
      Γ ⊢ app t1 t2 ∈ T2
  | T_True : forall Γ,
      Γ ⊢ tru ∈ Bool
  | T_False : forall Γ,
      Γ ⊢ fls ∈ Bool
  | T_Test : forall Γ t1 t2 t3 T,
      Γ ⊢ t1 ∈ Bool ->
      Γ ⊢ t2 ∈ T ->
      Γ ⊢ t3 ∈ T ->
      Γ ⊢ test t1 t2 t3 ∈ T
  | T_Unit : forall Γ,
      Γ ⊢ unit ∈ Unit
  | T_Sub : forall Γ t S T,
      Γ ⊢ t ∈ S ->
      S <: T ->
      Γ ⊢ t ∈ T
where "Γ '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

(* Properties *)

(* Inversion Lemmas for Subtyping *)

Lemma sub_inversion_Bool : forall U,
    U <: Bool -> U = Bool.
Proof.
  intros. remember Bool as V.
  induction H.
  - reflexivity.
  - subst. inversion H0; subst.
    + apply IHsubtype1. reflexivity.
    + assert (Bool = Bool). reflexivity.
      eapply IHsubtype2 in H3. subst.
      assert (Bool = Bool). reflexivity.
      eapply IHsubtype1 in H3. apply H3.
  - inversion HeqV.
  - inversion HeqV.
Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
    U <: Arrow V1 V2 ->
    exists U1 U2,
    U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof.
  intros.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction H; intros.
  - exists V1, V2.
    split. apply HeqV.
    split. constructor. constructor.
  - eapply IHsubtype2 in HeqV.
    destruct HeqV. destruct H1.
    destruct H1. destruct H2.
    eapply IHsubtype1 in H1.
    destruct H1. destruct H1.
    destruct H1. destruct H4.
    exists x1, x2.
    split. apply H1. split.
    eapply S_Trans. eapply H2. eapply H4.
    eapply S_Trans. eapply H5. eapply H3.
  - inversion HeqV.
  - inversion HeqV. subst. exists S1, S2.
    split. reflexivity. split. apply H. apply H0.
Qed.

Lemma canonical_forms_of_arrow_types : forall Γ s T1 T2,
    Γ ⊢ s ∈ (T1 ⇒ T2) ->
    value s ->
    exists x S1 s2,
    s = abs x S1 s2.
Proof.
  intros. remember (T1 ⇒ T2) as T.
  generalize dependent T2. generalize dependent T1.
  induction H; intros; subst.
  - inversion H0.
  - exists x, T11, t12. reflexivity.
  - inversion H0.
  - inversion HeqT.
  - inversion HeqT.
  - inversion H0.
  - inversion HeqT.
  - eapply sub_inversion_arrow in H1.
    destruct H1. destruct H1. destruct H1.
    eapply IHhas_type. apply H0. eauto.
Qed.

Lemma canonical_forms_of_Bool : forall Γ s,
    Γ ⊢ s ∈ Bool ->
    value s ->
    s = tru \/ s= fls.
Proof.
  intros. remember Bool as T.
  induction H.
  - inversion H0.
  - inversion HeqT.
  - inversion H0.
  - auto.
  - auto.
  - inversion H0.
  - inversion HeqT.
  - subst. eapply IHhas_type. apply sub_inversion_Bool. apply H1. apply H0.
Qed.

(* Progress *)

Theorem progress : forall t T,
    empty ⊢ t ∈ T ->
    value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Γ. revert HeqΓ.
  induction Ht; intros HeqΓ; subst...
  - inversion H.
  - right. destruct IHHt1; subst...
    + destruct IHHt2; subst...
      * destruct (canonical_forms_of_arrow_types empty t1 T1 T2).
        eauto. eauto. destruct H1. destruct H1.
        exists ([x := t2]x1). subst. eauto.
      * inversion H0. exists (app t1 x). eauto.
    + inversion H. exists (app x t2). eauto.
  - right. destruct IHHt1. reflexivity.
    eapply canonical_forms_of_Bool in H. 2: eauto.
    destruct H; subst.
    * exists t2. eauto.
    * exists t3. eauto.
    * destruct H. exists (test x t2 t3). eauto.
Qed.
    
(* Inversion Lemmas for Typing *)

Lemma typing_inversion_abs : forall Γ x S1 t2 T,
    Γ ⊢ (abs x S1 t2) ∈ T ->
    exists S2, (S1 ⇒ S2) <: T /\ (x |-> S1 ; Γ) ⊢ t2 ∈ S2.
Proof.
  intros.
  remember (abs x S1 t2) as f.
  induction H; inversion Heqf; subst.
  - exists T12. split. eauto. eauto.
  - destruct IHhas_type. reflexivity.
    exists x0. destruct H2. eauto.
Qed.

Lemma typing_inversion_var : forall Γ x T,
    Γ ⊢ (var x) ∈ T ->
    exists S, Γ x = Some S /\ S <: T.
Proof.
  intros. remember (var x) as t.
  induction H; intros; inversion Heqt; subst.
  - exists T. auto.
  - destruct IHhas_type. reflexivity.
    destruct H2. exists x0. split; eauto.
Qed.

Lemma typing_inversion_app : forall Γ t1 t2 T2,
    Γ ⊢ (app t1 t2) ∈ T2 ->
    exists T1,
      Γ ⊢ t1 ∈ (T1 ⇒ T2) /\ Γ ⊢ t2 ∈ T1.
Proof.
  intros. remember (app t1 t2) as t.
  induction H; intros; inversion Heqt; subst.
  - exists T1. eauto.
  - destruct IHhas_type; eauto.
    destruct H2. eauto.
Qed.

Lemma typing_inversion_true : forall Γ T,
    Γ ⊢ tru ∈ T -> Bool <: T.
Proof.
  intros. remember tru as t.
  induction H; intros; inversion Heqt; subst; eauto.
Qed.

Lemma typing_inversion_false : forall Γ T,
    Γ ⊢ fls ∈ T -> Bool <: T.
Proof.
  intros. remember fls as t.
  induction H; intros; inversion Heqt; subst; eauto.
Qed.

Lemma typing_inversion_if : forall Γ t1 t2 t3 T,
    Γ ⊢ (test t1 t2 t3) ∈ T ->
    Γ ⊢ t1 ∈ Bool /\
    Γ ⊢ t2 ∈ T /\
    Γ ⊢ t3 ∈ T.
Proof.
  intros. remember (test t1 t2 t3) as t.
  induction H; intros; inversion Heqt; subst; eauto.
  destruct IHhas_type; eauto. destruct H3. eauto.
Qed.

Lemma typing_inversion_unit : forall Γ T,
    Γ ⊢ unit ∈ T ->
    Unit <: T.
Proof.
  intros. remember unit as t.
  induction H; intros; inversion Heqt; subst; eauto.
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
    empty ⊢ (abs x S1 s2) ∈ (T1 ⇒ T2) ->
    T1 <: S1 /\ (x |-> S1 ; empty) ⊢ s2 ∈ T2.
Proof.
  intros.
  eapply typing_inversion_abs in H.
  inversion H. destruct H0. apply sub_inversion_arrow in H0.
  inversion H0 as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq. subst. eauto.
Qed.

(* Context Invariance *)

Inductive appears_free_in : string -> tm -> Prop :=
| afi_var : forall x,
    appears_free_in x (var x)
| afi_app1 : forall x t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (app t1 t2)
| afi_app2 : forall x t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (app t1 t2)
| afi_abs : forall x y T11 t12,
    y <> x ->
    appears_free_in x t12 ->
    appears_free_in x (abs y T11 t12)
| afi_test1 : forall x t1 t2 t3,
    appears_free_in x t1 ->
    appears_free_in x (test t1 t2 t3)
| afi_test2 : forall x t1 t2 t3,
    appears_free_in x t2 ->
    appears_free_in x (test t1 t2 t3)
| afi_test3 : forall x t1 t2 t3,
    appears_free_in x t3 ->
    appears_free_in x (test t1 t2 t3)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Γ Γ' t S ,
  Γ ⊢ t ∈ S ->
  (forall x, appears_free_in x t -> Γ x = Γ' x) ->
  Γ' ⊢ t ∈ S.
Proof.
  intros. generalize dependent Γ'.
  induction H; intros; eauto.
  - apply T_Var. rewrite <- H. symmetry. eapply H0. eauto.
  - apply T_Abs. apply IHhas_type.
    intros. unfold update. unfold t_update.
    destruct (eqb_stringP x x0). reflexivity.
    eapply H0. eauto.
  - constructor. eauto. eauto. eauto.
Qed.
    
Lemma free_in_context : forall x t T Γ,
    appears_free_in x t ->
    Γ ⊢ t ∈ T ->
    exists T', Γ x = Some T'.
Proof with eauto.
  intros x t T Γ Hfree Htype.
  induction Htype; subst; inversion Hfree; subst...
  - destruct (IHHtype H4) as [T Hctx].
    exists T.
    unfold update, t_update in Hctx.
    rewrite <- eqb_string_false_iff in H2.
    rewrite H2 in Hctx...
Qed.

(* Substitution *)

Lemma substitution_preserves_typing : forall Γ x U v t S,
    (x |-> U ; Γ) ⊢ t ∈ S ->
    empty ⊢ v ∈ U ->
    Γ ⊢ [x:=v]t ∈ S.
Proof.
  intros Γ x U v t S Htpt Htpv. generalize dependent S. generalize dependent Γ.
  induction t; intros; simpl.
  - rename s into y.
    edestruct typing_inversion_var as [T [Hctx Hsub]]. eapply Htpt.
    unfold update, t_update in Hctx.
    destruct (eqb_stringP x y) as [Hxy|Hxy]; eauto; subst.
    inversion Hctx; subst. apply context_invariance with empty.
    eauto. intros x Hcontra. destruct (free_in_context _ _ S empty Hcontra) as [T' HT'].
    eauto. inversion HT'.
  - destruct (typing_inversion_app _ _ _ _ Htpt) as [T1 [Htypt1 Htypt2]].
    eapply T_App. eauto. eauto.
  - rename s into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htpt) as [T2 [Hsub Htypt2]].
    apply T_Sub with (T1 ⇒ T2). apply T_Abs.
    destruct (eqb_stringP x y) as [Hxy | Hxy]; eauto.
    + eapply context_invariance. eauto. intros.
      subst. unfold update, t_update.
      destruct (eqb_string y x0). reflexivity. reflexivity.
    + eapply IHt. eapply context_invariance. eauto.
      intros. unfold update, t_update.
      destruct (eqb_stringP y x0). subst.
      rewrite <- eqb_string_false_iff in Hxy.
      rewrite Hxy. eauto. eauto.
    + eauto.
  - assert (Bool <: S).
    eapply typing_inversion_true. eauto. eauto.
  - assert (Bool <: S).
    eapply typing_inversion_false. eauto. eauto.
  - assert (H := typing_inversion_if _ _ _ _ _ Htpt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    eauto.
  - assert (Unit <: S). eapply typing_inversion_unit.
    eauto. eauto.
Qed.

(* Preservation *)

Theorem preservation : forall t t' T,
    empty ⊢ t ∈ T ->
    t --> t' ->
    empty ⊢ t' ∈ T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Γ.
  generalize dependent HeqΓ. generalize dependent t'.
  induction HT; intros; subst; inversion H; subst...
  - inversion H; subst.
    + destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T.
      eauto. eauto.
    + eauto.
    + eauto.
Qed.

