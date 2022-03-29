Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
Require Import NewMaps.
Require Import Smallstep.
Hint Constructors multi.

(* Language *)

Inductive ty : Type :=
| Bool : ty
| Arrow : ty -> ty -> ty
| Prod : ty -> ty -> ty
.

Notation "t1 '⇒' t2" := (Arrow t1 t2) (at level 40).

Inductive tm : Type :=
| var : string -> tm
| app : tm -> tm -> tm
| abs : string -> ty -> tm -> tm
| pair : tm -> tm -> tm
| fst : tm -> tm
| snd : tm -> tm
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm
.

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y => if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 => app (subst x s t1) (subst x s t2)
  | pair t1 t2 => pair (subst x s t1) (subst x s t2)
  | fst t1 => fst (subst x s t1)
  | snd t1 => snd (subst x s t1)
  | tru => tru
  | fls => fls
  | test t0 t1 t2 =>
      test (subst x s t0) (subst x s t1) (subst x s t2)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* Reduction *)

Inductive value : tm -> Prop :=
| v_abs : forall x T11 T12,
    value (abs x T11 T12)
| v_pair : forall v1 v2,
    value v1 ->
    value v2 ->
    value (pair v1 v2)
| v_tru : value tru
| v_fls : value fls
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T11 t12 v2,
    value v2 ->
    (app (abs x T11 t12) v2) --> [x := v2] t12
| ST_App1 : forall t1 t1' t2,
    t1 --> t1' ->
    (app t1 t2) --> (app t1' t2)
| ST_App2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    (app v1 t2) --> (app v1 t2')
| ST_Pair1 : forall t1 t1' t2,
    t1 --> t1' ->
    (pair t1 t2) --> (pair t1' t2)
| ST_Pair2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    (pair v1 t2) --> (pair v1 t2')
| ST_Fst : forall t1 t1',
    t1 --> t1' ->
    (fst t1) --> (fst t1')
| ST_FstPair : forall v1 v2,
    value v1 ->
    value v2 ->
    (fst (pair v1 v2)) --> v1
| ST_Snd : forall t1 t1',
    t1 --> t1' ->
    (snd t1) --> (snd t1')
| ST_SndPair : forall v1 v2,
    value v1 ->
    value v2 ->
    (snd (pair v1 v2)) --> v2
| ST_TestTrue : forall t1 t2,
    (test tru t1 t2) --> t1
| ST_TestFalse : forall t1 t2,
    (test fls t1 t2) --> t2
| ST_Test : forall t0 t0' t1 t2,
    t0 --> t0' ->
    (test t0 t1 t2) --> (test t0' t1 t2)
where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Lemma value_normal : forall t, value t -> step_normal_form t.
Proof.
  intros.
  induction H; intros [t' ST]; inversion ST; eauto.
Qed.

(* Typing *)

Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Γ x T,
    Γ x = Some T ->
    has_type Γ (var x) T
| T_Abs : forall Γ x T11 T12 t12,
    has_type (update Γ x T11) t12 T12 ->
    has_type Γ (abs x T11 t12) (T11 ⇒ T12)
| T_App : forall T1 T2 Γ t1 t2,
    has_type Γ t1 (T1 ⇒ T2) ->
    has_type Γ t2 T1 ->
    has_type Γ (app t1 t2) T2
| T_Pair : forall Γ t1 t2 T1 T2,
    has_type Γ t1 T1 ->
    has_type Γ t2 T2 ->
    has_type Γ (pair t1 t2) (Prod T1 T2)
| T_Fst : forall Γ t T1 T2,
    has_type Γ t (Prod T1 T2) ->
    has_type Γ (fst t) T1
| T_Snd : forall Γ t T1 T2,
    has_type Γ t (Prod T1 T2) ->
    has_type Γ (snd t) T2
| T_True : forall Γ,
    has_type Γ tru Bool
| T_False : forall Γ,
    has_type Γ fls Bool
| T_Test : forall Γ t0 t1 t2 T,
    has_type Γ t0 Bool ->
    has_type Γ t1 T ->
    has_type Γ t2 T ->
    has_type Γ (test t0 t1 t2) T
.

Hint Constructors has_type.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto.

Hint Extern 2 (_ = _) => compute; reflexivity.

(* Context Invariance *)

Inductive appears_free_in : string -> tm -> Prop :=
| afi_var : forall x,
    appears_free_in x (var x)
(* Why two rules, instead of a single rule that requires free both in t1 and t2*) 
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
| afi_pair1 : forall x t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (pair t1 t2)
| afi_pair2 : forall x t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (pair t1 t2)
| afi_fst : forall x t,
    appears_free_in x t ->
    appears_free_in x (fst t)
| afi_snd : forall x t,
    appears_free_in x t ->
    appears_free_in x (snd t)
| afi_test0 : forall x t0 t1 t2,
    appears_free_in x t0 ->
    appears_free_in x (test t0 t1 t2)
| afi_test1 : forall x t0 t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (test t0 t1 t2)
| afi_test2 : forall x t0 t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (test t0 t1 t2)
.

Hint Constructors appears_free_in.

Definition closed (t : tm) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Γ Γ' t S,
    has_type Γ t S ->
    (forall x, appears_free_in x t -> Γ x = Γ' x) ->
    has_type Γ' t S.
Proof.
  intros. generalize dependent Γ'.
  induction H; intros Γ' Heq; eauto.
  - (* T_Var *)
    apply T_Var. rewrite <- H. symmetry. eauto.
  - (* T_Abs *)
    apply T_Abs. apply IHhas_type. intros y Hafi.
    unfold update, t_update. destruct (eqb_stringP x y).
    reflexivity. eapply Heq. eauto.
  - (* T_Pair *)
    apply T_Pair. eauto. eauto.
  - eapply T_Test. eauto. eauto. eauto.
Qed.

Lemma free_in_context : forall x t T Γ,
    appears_free_in x t ->
    has_type Γ t T ->
    exists T', Γ x = Some T'.
Proof.
  intros x t T Γ Hafi Htp.
  induction Htp; inversion Hafi; eauto; subst.
  - (* T_Abs *)
    destruct IHHtp as [T' Hctx]. eapply H4.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx.
    exists T'. apply Hctx. apply H2.
Qed.

Corollary typable_empty_closed : forall t T,
    has_type empty t T ->
    closed t.
Proof.
  intros. unfold closed.
  intros x H1.
  destruct (free_in_context _ _ _ _ H1 H).
  inversion H0.
Qed.

(* Preservation *)

Lemma subst_preserves_typing : forall Γ x U v t S,
    has_type (update Γ x U) t S ->
    has_type empty v U ->
    has_type Γ ([x := v]t) S.
Proof with eauto.
  intros Γ x U v t S Htypt Htypv.
  generalize dependent Γ. generalize dependent S.
  induction t; intros S Γ Htypt; simpl; inversion Htypt; subst; eauto...
  - (* var *)
    rename s into y. unfold update, t_update in H1.
    destruct (eqb_stringP x y).
    + (* x = y *)
      inversion H1. subst.
      eapply context_invariance. apply Htypv.
      intros. destruct (free_in_context _ _ _ _ H Htypv). inversion H0.
    + (* x ≠ y *)
      eapply T_Var. apply H1.
  - (* abs *)
    rename s into y.
    apply T_Abs. destruct (eqb_stringP x y).
    + (* x = y *)
      eapply context_invariance.
      eapply H4. intros. unfold update, t_update. subst.
      destruct (eqb_string y x0). eauto. eauto.
    + (* x ≠ y *)
      apply IHt. eapply context_invariance. apply H4.
      intros. unfold update, t_update.
      destruct (eqb_stringP y x0). subst.
      rewrite false_eqb_string. reflexivity.
      apply n. reflexivity.
Qed.

Theorem preservation : forall t t' T,
    has_type empty t T ->
    t --> t' ->
    has_type empty t' T.
Proof with eauto.
  intros t t' T HT. remember (@empty ty) as Γ.
  generalize dependent HeqΓ. generalize dependent t'.
  induction HT; intros t' HeqΓ HE; subst; inversion HE; subst...
  - (* app *)
    inversion HE; subst...
    + apply subst_preserves_typing with T1...
      inversion HT1...
  - inversion HT...
  - inversion HT...
Qed.

(* Determinisitc *)

Lemma step_deterministic : deterministic step.
Proof.
Admitted.

(* Normalization *)

Definition halts (t : tm) : Prop :=
  exists t', t -->* t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  eauto. auto.
Qed.

(* Key in SN: find a strong enough inductive hypothesis 
   For each type T, define a set R_T of closed terms of type T.
   Use a relation R and write R T t when t is in R_T.
   The sets R_T are sometimes called saturated sets or reducibility candidates.
 *)

(* strict positivity requirement:
   For inductive definitions, the type being defined must not occur to the
   left of an arrow in the type of a constructor argument.

Inductive R : ty -> tm -> Prop :=
| R_Bool : forall t, has_type empty t Bool ->
                halts t ->
                R Bool t
| R_Arrow : forall T1 T2 t, has_type empty t (T1 ⇒ T2) ->
                       halts t ->
                       (forall s, R T1 s -> R T2 (app t s)) ->
                       R (T1 ⇒ T2) t
.
 *)

Fixpoint R (T : ty) (t : tm) {struct T} : Prop :=
  has_type empty t T /\ halts t /\
  (match T with
   | Bool => True
   | (T1 ⇒ T2) => (forall s, R T1 s -> R T2 (app t s))
   | Prod T1 T2 => forall t1 t2, R T1 t1 /\ R T2 t2
   end).

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  intros. unfold R in H. destruct T.
  - inversion H. inversion H1. assumption.
  - inversion H. inversion H1. assumption.
  - inversion H. inversion H1. assumption.
Qed.

Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
Proof.
  intros.
  unfold R in H.
  destruct T; inversion H; inversion H1; assumption.
Qed.

(* Sketch:
   Need to show that every well-typed term of type T is an element of R_T;
   and R_T implies halts.
 *)

(* Membership in R_T is invariant under reduction *)

Lemma step_preserves_halting : forall t t',
    (t --> t') ->
    (halts t <-> halts t').
Proof.
  intros. split; intros; unfold halts in *.
  - destruct H0. destruct H0.
    inversion H0; subst.
    + exfalso. apply value_normal in H1.
      unfold normal_form in H1. apply H1.
      exists t'. apply H.
    + rewrite (step_deterministic _ _ _  H H2).
      exists x. eauto.
  - destruct H0. destruct H0.
    exists x. split; eauto.
Qed.

Lemma step_preserves_R : forall T t t',
    (t --> t') ->
    R T t ->
    R T t'.
Proof.
  induction T; intros; destruct H0 as [H1 [H2 H3]]; unfold R.
  - split. eapply preservation. apply H1.
    apply H. split. eapply (step_preserves_halting _ _ H).
    apply H2. apply H3.
  - fold R. split. eapply preservation. apply H1.
    apply H. split. eapply (step_preserves_halting _ _ H).
    apply H2. intros. eapply IHT2.
    apply ST_App1. apply H. apply H3.
    apply H0.
  - fold R. split. eapply preservation. apply H1.
    apply H. split. eapply (step_preserves_halting _ _ H).
    apply H2. apply H3.
Qed.

Lemma multistep_preservers_R : forall T t t',
    (t -->* t') ->
    (R T t) ->
    (R T t').
Proof.
  intros T t t' STM.
  induction STM; intros.
  - apply H.
  - apply IHSTM. eapply step_preserves_R. apply H. apply H0.
Qed.

Lemma step_preserves_R_rev : forall T t t',
    has_type empty t T ->
    (t --> t') ->
    R T t' ->
    R T t.
Proof.
  induction T; intros; unfold R in *; destruct H1; destruct H2.
  - split. apply H.
    split. eapply (step_preserves_halting _ _ H0). apply H2. apply H3.
  - fold R in *. split. apply H.
    split. eapply (step_preserves_halting _ _ H0). apply H2.
    intros. eapply IHT2. eapply T_App.
    apply H. apply R_typable_empty. apply H4. apply ST_App1. apply H0.
    apply H3. apply H4.
  - fold R in *. split. apply H.
    split. apply (step_preserves_halting _ _ H0). apply H2.
    apply H3.
Qed.

Lemma multistep_preserves_R_rev : forall T t t',
    has_type empty t T ->
    (t -->* t') ->
    R T t' ->
    R T t.
Proof.
  intros T t t' HST MST.
  induction MST.
  - eauto.
  - intros. eapply step_preserves_R_rev.
    apply HST. apply H. apply IHMST. eapply preservation.
    apply HST. apply H. apply H0.
Qed.

(* Closed instances of Term of Type T Belong to R_T *)

(* Multisubstitutions, Multi-Extensions, and Instantiations *)

(* multisubstitution *)

Definition env := list (string * tm).

Fixpoint msubst (ss : env) (t : tm) {struct ss} : tm :=
  match ss with
  | nil => t
  | (x, s)::ss' =>
    msubst ss' ([x := s] t)
  end.

(* type assignment *)

Definition tass := list (string * ty).

Fixpoint mupdate (Γ : context) (xts : tass) : context :=
  match xts with
  | nil => Γ 
  | (x, v)::xts' => update (mupdate Γ xts') x v
  end.

Fixpoint lookup {X : Set} (k : string) (l : list (string * X)) {struct l} : option X :=
  match l with
  | nil => None
  | (j, x)::l' =>
    if eqb_string j k then Some x else lookup k l'
  end.

Fixpoint drop {X : Set} (n : string) (nxs : list (string * X)) {struct nxs} : list (string * X) :=
  match nxs with
  | nil => nil
  | (n', x)::nxs' =>
    if eqb_string n' n then drop n nxs'
    else (n', x) :: (drop n nxs')
  end.

(* Instantiations *)

Inductive instantiation : tass -> env -> Prop :=
| V_nil : instantiation nil nil
| V_cons : forall x T v c e,
    value v ->
    R T v ->
    instantiation c e ->
    instantiation ((x, T)::c) ((x, v)::e)
.

(* Some facts of substitution *)

Lemma vacuous_subst : forall t x,
    ~ appears_free_in x t ->
    forall t', [x := t'] t = t.
Proof.
Admitted.

Lemma subst_closed : forall t,
    closed t ->
    forall x t', [x := t']t = t.
Proof.
Admitted.

Lemma subst_not_afi : forall t x v,
    closed v -> ~ appears_free_in x ([x := v] t).
Proof.
Admitted.

Lemma duplicate_subst : forall t' x t v,
    closed v -> [x:=t]([x:=v]t') = [x:=v]t'.
Proof.
Admitted.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    [x1:=v1]([x:=v]t) = [x:=v]([x1:=v1]t).
Proof.
Admitted.

(* Properties of Multi-substitution *)

Lemma msubst_closed : forall t,
    closed t ->
    forall ss, msubst ss t = t.
Proof.
  induction ss.
  - reflexivity.
  - simpl. destruct a.
    rewrite subst_closed. apply IHss. apply H.
Qed.

Fixpoint closed_env (ρ : env) {struct ρ} :=
  match ρ with
  | nil => True
  | (x, t) :: ρ' => closed t /\ closed_env ρ'
  end.

Lemma subst_msubst : forall env x v t,
    closed v ->
    closed_env env ->
    msubst env ([x := v]t) = [x := v](msubst (drop x env) t).
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (eqb_stringP s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.

Lemma msubst_var : forall ss x,
    closed_env ss ->
    msubst ss (var x) =
    match lookup x ss with
    | Some t => t
    | None => var x
    end.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. simpl.
    destruct (eqb_stringP s x).
    apply msubst_closed.
    inversion H. apply H0.
    apply IHss. inversion H. apply H1.
Qed.

Lemma msubst_abs: forall ss x T t,
  msubst ss (abs x T t) = abs x T (msubst (drop x ss) t).
Proof.
  induction ss; intros.
  reflexivity. destruct a.
  simpl. destruct (eqb_string s x); simpl; auto.
Qed.

Lemma msubst_app : forall ss t1 t2,
    msubst ss (app t1 t2) = app (msubst ss t1) (msubst ss t2).
Proof.
Admitted.

Lemma msubst_pair : forall ss t1 t2,
    msubst ss (pair t1 t2) = app (msubst ss t1) (msubst ss t1).
Proof.
Admitted.

(* Properties of Multi-extensions *)

Lemma mupdate_lookup : forall (c : tass) (x : string),
    lookup x c = (mupdate empty c) x.
Proof.
Admitted.

Lemma mupdate_drop : forall (c : tass) Γ x x',
    mupdate Γ (drop x c) x' =
    if eqb_string x x' then Γ x' else mupdate Γ c x'.
Proof.
Admitted.

(* Properties of Instantiations *)

Lemma instantiation_domains_match : forall {c} {e},
    instantiation c e ->
    forall {x} {T},
      lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
Admitted.

Lemma instantiation_env_closed : forall c e,
    instantiation c e -> closed_env e.
Proof. Admitted.

Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
Proof.
Admitted.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof. Admitted.

(* Congruence Lemmas on Multistep *)

Lemma multistep_App2 : forall v t t',
    value v ->
    (t -->* t') ->
    (app v t) -->* (app v t').
Proof.
  intros.
  induction H0.
  - constructor.
  - eapply multi_step.
    eapply ST_App2. apply H. apply H0. apply IHmulti.
Qed.

(* The R Lemma *)

Lemma msubst_preserves_typing : forall c e,
    instantiation c e ->
    forall G t S,
      has_type (mupdate G c) t S ->
      has_type G (msubst e t) S.
Proof.
Admitted.

Lemma msubst_R : forall c env t T,
    has_type (mupdate empty c) t T ->
    instantiation c env ->
    R T (msubst env t).
Proof.
Admitted.

(* The normalization theorem *)

Theorem normalization : forall t T,
    has_type empty t T ->
    halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  eapply R_halts.
  eapply (msubst_R nil). simpl. apply H.
  constructor.
Qed.
