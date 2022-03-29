Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

(* Maps *)

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.
Notation "x '!->' v ';' m" := (t_update m x v) (at level 100, v at next level, right associativity).

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A := t_empty None.
Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  (x !-> Some v ; m).
Notation "x '⊢>' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).
Notation "x '⊢>' v" := (update empty x v) (at level 100).

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

(* Relations *)

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition deterministic {X} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition normal_form {X} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* Strong Normalization of STLC *)

Inductive ty : Type :=
| ty_arrow : ty -> ty -> ty
.

Inductive tm : Type :=
| tm_var : string -> tm
| tm_app : tm -> tm -> tm
| tm_abs : string -> ty -> tm -> tm
.

Declare Custom Entry stlc.

Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Coercion tm_var : string >-> tm.

(* Substitution *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
    if String.eqb x y then s else t
  | tm_abs y T t1 =>
    if String.eqb x y then t else tm_abs y T (subst x s t1)
  | tm_app t1 t2 =>
    tm_app (subst x s t1) (subst x s t2)
  end.
    
Inductive value : tm -> Prop :=
| v_abs : forall x T2 t1, value (tm_abs x T2 t1).

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
      value v2 ->
      tm_app (tm_abs x T2 t1) v2 --> (subst x v2 t1)
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
where "t '-->' t'" := (step t t').

Hint Constructors step : core.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Notation step_normal_form := (normal_form step).

Lemma value_normal : forall t, value t -> step_normal_form t.
Proof with eauto.
  intros t H; induction H; intros [t' ST]; inversion ST...
Qed.

Definition context := partial_map ty.
Reserved Notation "Γ '⊢' t '∈' T" (at level 40, t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Γ x T1,
    Γ x = Some T1 ->
    Γ ⊢ x ∈ T1
| T_Abs : forall Γ x T1 T2 t1,
    (x ⊢> T2 ; Γ) ⊢ t1 ∈ T1 ->
    Γ ⊢ (tm_abs x T2 t1) ∈ (ty_arrow T2 T1)
| T_App : forall T1 T2 Γ t1 t2,
    Γ ⊢ t1 ∈ (ty_arrow T2 T1) ->
    Γ ⊢ t2 ∈ T2 ->
    Γ ⊢ (tm_app t1 t2) ∈ T1
where "Γ '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type : core.
Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

(* Weakening *)

Lemma weakening : forall Γ Γ' t T,
    inclusion Γ Γ' ->
    Γ ⊢ t ∈ T ->
    Γ' ⊢ t ∈ T.
Proof.
Admitted.

Lemma weakening_empty : forall G t T,
    empty ⊢ t ∈ T ->
    G ⊢ t ∈ T.
Proof.
  intros. eapply weakening. 2: apply H. discriminate.
Qed.

(* Preservation *)

Lemma subst_preserves_typing : forall G x U t v T,
    (x ⊢> U ; G) ⊢ t ∈ T ->
    empty ⊢ v ∈ U ->
    G ⊢ (subst x v t) ∈ T.
Proof. Admitted.

Theorem preservation : forall t t' T,
    empty ⊢ t ∈ T ->
    t --> t' ->
    empty ⊢ t' ∈ T.
Proof. Admitted.

(* Context invariance *)

Inductive appears_free_in : string -> tm -> Prop :=
| afi_var : forall (x : string),
    appears_free_in x x
| afi_app1 : forall x t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (tm_app t1 t2)
| afi_app2 : forall x t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (tm_app t1 t2)
| afi_abs : forall x y T11 t12,
    y <> x ->
    appears_free_in x t12 ->
    appears_free_in x (tm_abs y T11 t12).

Hint Constructors appears_free_in : core.

Definition closed (t : tm) := forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Γ Γ' t S,
    Γ ⊢ t ∈ S ->
    (forall x, appears_free_in x t -> Γ x = Γ' x) ->
    Γ' ⊢ t ∈ S.
Proof. Admitted.
  
Lemma free_in_context : forall x t T Γ,
    appears_free_in x t ->
    Γ ⊢ t ∈ T ->
    exists T', Γ x = Some T'.
Proof. Admitted.

Corollary typable_empty_closed : forall t T,
    empty ⊢ t ∈ T ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.

Lemma step_deterministic : deterministic step.
Proof. Admitted.

(* Normalization *)

Definition halts (t : tm) : Prop :=
  exists t', t -->* t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros. unfold halts. exists v. split.
  - apply multi_refl.
  - assumption.
Qed.

(* This doesn't work:
Inductive R : ty -> tm -> Prop :=
| R_arrow : forall T1 T2 t,
    empty ⊢ t ∈ (ty_arrow T1 T2) ->
    halts t ->
    (forall t', R T1 t' -> R T2 (tm_app t t')) ->
    R (ty_arrow T1 T2) t.
 *)

Fixpoint R_Halt (T : ty) (t : tm) : Prop :=
  empty ⊢ t ∈ T /\ halts t /\
  (match T with
   | ty_arrow T1 T2 => (forall s, R_Halt T1 s -> R_Halt T2 (tm_app t s))
   end).

Lemma R_Halt_halts : forall {T t}, R_Halt T t -> halts t.
Proof.
  intros. destruct T. unfold R_Halt in H. intuition.
Qed.

Lemma R_Halt_typable_empty : forall {T t}, R_Halt T t -> empty ⊢ t ∈ T.
Proof.
  intros. destruct T. unfold R_Halt in H. intuition.
Qed.

(* Membership in R_Halt is invariant under reduction *)

Lemma step_preserves_halting : forall t t',
    (t --> t') -> (halts t <-> halts t').
Proof.
Admitted.

Lemma step_preserves_R_Halt : forall T t t',
    (t --> t') -> R_Halt T t -> R_Halt T t'.
Proof.
  intro T. induction T; intros.
  unfold R_Halt in H0. destruct H0. destruct H1.
  split. eapply preservation. eauto. eauto.
  split. apply (@step_preserves_halting t t'). auto. intuition.
  intros. eapply IHT2. apply ST_App1. eauto.
  apply H2. fold R_Halt. apply H3.
Qed.

Lemma multistep_preserves_R_Halt : forall T t t',
    (t -->* t') -> R_Halt T t -> R_Halt T t'.
Proof. Admitted.

Lemma step_preserves_R_Halt' : forall T t t',
    empty ⊢ t ∈ T ->
    (t --> t') ->
    R_Halt T t' -> R_Halt T t.
Proof. Admitted.

Lemma multistep_preserves_R_Halt' : forall T t t',
    empty ⊢ t ∈ T ->
    (t -->* t') ->
    R_Halt T t' -> R_Halt T t.
Proof. Admitted.

(* Closed _instances_ of terms of type T belong to R_Halt *)

(* Generalizing the induction hypothesis: instead of proving
a statement involving a closed term, we generalize it to cover
all closed instances of an open term t. *)

(* Multiple substitution, multiple extension *)

Definition env := list (string * tm).

Fixpoint msubst (ρ : env) (t : tm) : tm :=
  match ρ with
  | nil => t
  | (x, s) :: ρ' => msubst ρ' (subst x s t)
  end.

Definition tass := list (string * ty).

Fixpoint mupdate (Γ : context) (xts : tass) : context :=
  match xts with
  | nil => Γ
  | (x, v) :: xts' => update (mupdate Γ xts') x v
  end.

Fixpoint lookup {X : Set} (k : string) (l : list (string * X)) : option X :=
  match l with
  | nil => None
  | (j, x) :: l' =>
      if String.eqb j k then Some x else lookup k l'
  end.

Fixpoint drop {X : Set} (n : string) (nxs : list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | (n', x) :: nxs' =>
      if String.eqb n' n then drop n nxs' else (n', x) :: (drop n nxs')
  end.

Inductive instantiation : tass -> env -> Prop :=
| V_nil : instantiation nil nil
| V_cons : forall x T v c e,
    value v ->
    R_Halt T v ->
    instantiation c e ->
    instantiation ((x, T)::c) ((x, v)::e)
.

Lemma vacuous_substitution : forall t x,
    ~ appears_free_in x t ->
    forall t', subst x t' t = t.
Proof. Admitted.

Lemma subst_closed : forall t,
    closed t ->
    forall x t', subst x t' t = t.
Proof. Admitted.

Lemma subst_not_afi : forall t x v,
    closed v -> ~ appears_free_in x (subst x v t).
Proof. Admitted.

Lemma duplicate_subst : forall t' x t v,
    closed v -> subst x t (subst x v t') = subst x v t'.
Proof. Admitted.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    subst x1 v1 (subst x v t) = subst x v (subst x1 v1 t).
Proof. Admitted.

Lemma msubst_closed : forall t , closed t -> forall ss, msubst ss t = t.
Proof.
  induction ss. simpl. reflexivity.
  simpl. destruct a.
  rewrite subst_closed; assumption.
Qed.

Fixpoint closed_env (ρ : env) :=
  match ρ with
  | nil => True
  | (x, t) :: ρ' => closed t /\ closed_env ρ'
  end.

Lemma subst_msubst : forall ρ x v t,
    closed v ->
    closed_env ρ ->
    msubst ρ (subst x v t) = subst x v (msubst (drop x ρ) t).
Proof.
  induction ρ; intros; auto.
  destruct a. simpl.
  inversion H0. destruct (String.eqb s x) eqn:Heq.
  - apply String.eqb_eq in Heq. subst.
    rewrite duplicate_subst; eauto.
  - apply String.eqb_neq in Heq. rewrite swap_subst; eauto.
Qed.

Lemma msubst_var : forall ss x,
    closed_env ss ->
    msubst ss (tm_var x) =
    match lookup x ss with
    | Some t => t
    | None => tm_var x
    end.
Proof. Admitted.

Lemma msubst_abs : forall ss x T t,
    msubst ss (tm_abs x T t) = tm_abs x T (msubst (drop x ss) t).
Proof. Admitted.

Lemma msubst_app : forall ss t1 t2,
    msubst ss (tm_app t1 t2) = tm_app (msubst ss t1) (msubst ss t2).
Proof. Admitted.

(* Properties of Multi-Extensions *)

Lemma mupdate_lookup : forall (c : tass) (x : string),
    lookup x c = (mupdate empty c) x.
Proof. Admitted.

Lemma mupdate_drop : forall (c : tass) Γ x x',
    mupdate Γ (drop x c) x' =
    if String.eqb x x' then Γ x' else mupdate Γ c x'.
Proof. Admitted.

(* Properties of Instantiation *)

Lemma ins_domains_match : forall {c e},
    instantiation c e ->
    forall {x T}, lookup x c = Some T -> exists t, lookup x e = Some t.
Proof. Admitted.

Lemma ins_env_closed : forall {c e},
    instantiation c e -> closed_env e.
Proof. Admitted.

Lemma ins_R_Halt : forall {c e},
    instantiation c e ->
    forall x t T, lookup x c = Some T -> lookup x e = Some t -> R_Halt T t.
Proof. Admitted.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof. Admitted.

(* Congruence Lemmas on Multistep *)

Lemma multistep_App2 : forall v t t',
    value v -> (t -->* t') ->
    (tm_app v t) -->* (tm_app v t').
Proof.
  intros. induction H0.
  apply multi_refl. eapply multi_step. apply ST_App2. eauto. eauto. eauto.
Qed.

(* The R_Halt Lemma *)

Lemma msubst_preserves_typing : forall c e,
    instantiation c e ->
    forall Γ t S, (mupdate Γ c) ⊢ t ∈ S ->
             Γ ⊢ (msubst e t) ∈ S.
Proof. Admitted.

Lemma msubst_R_Halt : forall c env t T,
    (mupdate empty c) ⊢ t ∈ T ->
    instantiation c env ->
    R_Halt T (msubst env t).
Proof. Admitted.

Theorem normalization : forall t T,
    empty ⊢ t ∈ T ->
    halts t.
Proof.
  intros. replace t with (msubst nil t) by reflexivity.
  apply (@R_Halt_halts T).
  apply (msubst_R_Halt nil). eauto.
  eapply V_nil.
Qed.
