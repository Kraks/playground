-- STLC
-- locally nameless where free variables are de Bruijn levels
-- call-by-value small-step semantics and logical relations
-- safety and termination

import Mathlib.Data.Finset.Sort
import STLC.Env

namespace Smallstep_LR

inductive ty : Type
| arrow : ty → ty → ty

inductive tm : Type
| bvar : ℕ → tm
| fvar : ℕ → tm
| abs : tm → tm
| app : tm → tm → tm

abbrev tenv := List ty
abbrev venv := List tm

-- combine open and subst: t1[n ↦ t2]
@[simp]
def openSubst (t1: tm) (n: ℕ) (t2: tm) : tm :=
  match t1 with
  | .bvar x =>
    if x = n then t2
    else if n < x then .bvar (x - 1)
    else .bvar x
  | .fvar x => .fvar x
  | .abs t1 => .abs (openSubst t1 (n + 1) t2)
  | .app t11 t12 =>
    .app (openSubst t11 n t2) (openSubst t12 n t2)

#eval openSubst (.bvar 0) 0 (.fvar 0)
#eval openSubst (.abs (.bvar 1)) 0 (.fvar 0)
#eval openSubst (.app (.abs (.app (.bvar 1) (.bvar 0))) (.bvar 0)) 0 (.fvar 0)
#eval openSubst (.bvar 1) 0 (.fvar 0)

@[simp]
def substF (Δ: venv) (t: tm) : tm :=
  match t with
  | .bvar _ => t
  | .fvar x =>
    match indexr x Δ with
    | none => t
    | some t' => t'
  | .abs t1 => .abs (substF Δ t1)
  | .app t11 t12 => .app (substF Δ t11) (substF Δ t12)

@[simp]
def closedF (t: tm) (n: ℕ) : Prop :=
  match t with
  | .bvar _ => true
  | .fvar x => x < n
  | .abs t1 => closedF t1 n
  | .app t11 t12 => closedF t11 n ∧ closedF t12 n

@[simp]
def closedB (t: tm) (n: ℕ) : Prop :=
  match t with
  | .bvar x => x < n
  | .fvar _ => true
  | .abs t1 => closedB t1 (n + 1)
  | .app t11 t12 => closedB t11 n ∧ closedB t12 n

lemma openClosed : ∀ t n m,
  closedB (openSubst t m (.fvar n)) m →
  closedB t (m+1) := by
  intros t; induction t <;> intros n m h <;> simp
  case bvar x =>
    by_cases hx: (x = m)
    . omega
    . by_cases hx': (x < m)
      omega; unfold openSubst at h;
      rw [if_neg hx] at h; have hx'' : (m < x) := by omega;
      simp [hx''] at h; omega
  case abs t ih =>
    apply ih n (m+1); unfold openSubst at h; simp at h; assumption
  case app t1 t2 ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2

lemma openClosed': ∀ t n m,
    closedB t (m+1) → closedB (openSubst t m (.fvar n)) m := by
  intros t; induction t <;> intros n m h <;> simp
  case bvar x =>
    by_cases hx: (x = m)
    . simp [hx]
    . rw [if_neg hx]; by_cases hx': (m < x)
      . simp at h; omega
      . rw [if_neg hx']; simp; omega
  case abs t ih =>
    apply ih n (m+1); simp at h; assumption
  case app t1 t2 ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2

lemma closedBOpenId: ∀ t1 t2 n,
  closedB t1 n -> openSubst t1 n t2 = t1 := by
  intros t1; induction t1 <;> intros t2 n h <;> simp
  case bvar x =>
    by_cases hx: (x = n)
    . simp at h; omega
    . rw [if_neg hx]; by_cases hx': (n < x)
      . simp at h; omega
      . simp [if_neg hx']
  case abs t ih => simp at h; apply ih; assumption
  case app t1 t2 ih1 ih2 =>
    apply And.intro
    . apply ih1; apply h.1
    . apply ih2; apply h.2

lemma closedBInc: ∀ t n n1,
    closedB t n -> n <= n1 -> closedB t n1 := by
  intros t; induction t <;> intros n n1 hcl hle <;> simp
  case bvar x => simp at hcl; omega
  case abs t ih => simp at hcl; apply ih; apply hcl; omega
  case app t1 t2 ih1 ih2 =>
    apply And.intro
    . apply ih1; apply hcl.1; omega
    . apply ih2; apply hcl.2; omega

lemma substFOpenComm : ∀ t t1 Δ n, closedF t Δ.length →
  (∀ x t1, indexr x Δ = some t1 → closedB t1 0) →
  substF (t1::Δ) (openSubst t n (.fvar Δ.length)) =
  openSubst (substF Δ t) n t1 := by
  intros t t1 Δ n h; revert n; induction t <;> intros n hc <;> simp
  case bvar x =>
    by_cases hx: (x = n)
    . simp [hx]
    . rw [if_neg hx]; rw [if_neg hx]
      by_cases hx': (n < x)
      simp [hx']; rw [if_neg hx']; simp
  case fvar x =>
    have h' := indexrSome Δ x h
    rcases h' with ⟨v, hidx⟩; rw [hidx]; simp;
    have hx : ¬(x = Δ.length) := by simp at h; omega
    rw [if_neg hx]; simp;
    rw [closedBOpenId]; apply closedBInc; apply hc; apply hidx; omega
  case abs t ih => apply ih; simp at h; assumption; apply hc
  case app t1 t2 ih1 ih2 =>
    simp at h; apply And.intro
    . apply ih1; apply h.1; assumption
    . apply ih2; apply h.2; assumption

lemma substFClosedBComm: ∀ t Δ n,
  (forall x t1, indexr x Δ = some t1 -> closedB t1 0) ->
  (closedB t n) -> (closedB (substF Δ t) n) := by
  intros t; induction t <;> intros E n hidx hcl <;> simp
  case bvar x => simp at hcl; assumption
  case fvar x =>
    generalize h : indexr x E = v
    cases v <;> simp
    case some v => apply closedBInc; apply hidx; apply h; omega
  case abs t ih => apply ih; apply hidx; simp at hcl; assumption
  case app t1 t2 ih1 ih2 =>
    rcases hcl with ⟨hcl1, hcl2⟩
    apply And.intro
    . apply ih1; apply hidx; assumption
    . apply ih2; apply hidx; assumption

@[simp]
def binds x τ (Γ : tenv) := (indexr x Γ = some τ)

inductive hasType : tenv → tm → ty → Prop
| t_var : ∀ Γ x τ, binds x τ Γ → hasType Γ (.fvar x) τ
| t_abs : ∀ Γ t τ₁ τ₂,
  hasType (τ₁::Γ) (openSubst t 0 (.fvar Γ.length)) τ₂ →
  closedF t Γ.length →
  hasType Γ (.abs t) (ty.arrow τ₁ τ₂)
| t_app : ∀ Γ t₁ t₂ τ₁ τ₂,
  hasType Γ t₁ (.arrow τ₁ τ₂) →
  hasType Γ t₂ τ₁ →
  hasType Γ (.app t₁ t₂) τ₂

inductive value : tm → Prop
| v_abs : ∀ t, value (.abs t)

inductive step : tm → tm → Prop
| st_beta : ∀ t v,
  value v →
  step (.app (.abs t) v) (openSubst t 0 v)
| st_app1 : ∀ t1 t1' t2,
  step t1 t1' →
  step (.app t1 t2) (.app t1' t2)
| st_app2 : ∀ t1 t2 t2',
  step t2 t2' →
  step (.app t1 t2) (.app t1 t2')

inductive stepn : tm → tm → Prop
| stepn_refl : ∀ t, stepn t t
| stepn_multi : ∀ t1 t2 t3, stepn t1 t2 → step t2 t3 → stepn t1 t3

lemma stepnApp1 : ∀ t1 t1' t2, stepn t1 t1' → stepn (.app t1 t2) (.app t1' t2) := by
  intros t1 t1' t2 h; induction h
  . constructor
  . case _ hstn hst ih => constructor; assumption; apply step.st_app1; assumption

lemma stepnApp2 : ∀ t1 t2 t2', stepn t2 t2' → stepn (.app t1 t2) (.app t1 t2') := by
  intros t1 t2 t2' h; induction h
  . constructor
  . case _ hstn hst ih => constructor; assumption; apply step.st_app2; assumption

lemma stepnTrans : ∀ t1 t2 t3, stepn t1 t2 → stepn t2 t3 → stepn t1 t3 := by
  intros t1 t2 t3 h1 h2; induction h2
  . assumption
  . case _ _ _ hstn hst ih =>
    apply stepn.stepn_multi; apply ih; assumption

@[simp]
def valType : tm → ty → Prop
| .abs t2, .arrow τ1 τ2 =>
  ∀ v1, valType v1 τ1 ∧ closedB v1 0 →
  ∃ v2, stepn (openSubst t2 0 v1) v2 ∧ closedB v2 0 ∧ valType v2 τ2
| _, _ => false

lemma valTypeValue : ∀ t τ, valType t τ → value t := by
  intros t τ h; cases t <;> try simp at h
  next t => apply value.v_abs

@[simp]
def expType (t : tm) (τ : ty) : Prop := ∃ v, stepn t v ∧ closedB v 0 ∧ valType v τ

@[simp]
def envType (Δ : venv) (Γ : tenv) : Prop :=
  Δ.length = Γ.length ∧
  ∀ τ x, binds x τ Γ →
  ∃ v, indexr x Δ = some v ∧ closedB v 0 ∧ valType v τ

lemma envTypeMt : envType [] [] := by simp

lemma envTypeExtend : ∀ Δ Γ v τ,
  envType Δ Γ → closedB v 0 → valType v τ → envType (v::Δ) (τ::Γ) := by
  intros Δ Γ v τ henv hcl hv; simp; simp at henv
  apply And.intro
  . apply henv.1
  . intros τ1 x bd; rcases henv with ⟨hlen, h⟩
    by_cases hx: (x = Γ.length)
    . rw [hx] at bd; simp at bd;
      rw [hlen]; simp [hx]; rw [<-bd]; apply And.intro; assumption; assumption
    . rw [if_neg hx] at bd; rw [hlen]; rw [if_neg hx]
      apply h; assumption

lemma envTypeClosed : ∀ Δ Γ, envType Δ Γ →
  (∀ x t1, indexr x Δ = some t1 → closedB t1 0) := by
  intros Δ Γ henv; rcases henv with ⟨hlen, h⟩
  intros x t1 hidx;
  have hx : (x < Δ.length) := by apply indexrSome'; exists t1
  rw [hlen] at hx; have hidx' := indexrSome Γ x hx
  rcases hidx' with ⟨τ, hidx'⟩;
  have ⟨t2, hidx'', hval⟩  := h τ x hidx'
  rcases hval with ⟨hcl, _⟩; rw [hidx] at hidx''; cases hidx''; assumption

@[simp]
def semType (Γ : tenv) (t : tm) (τ : ty) : Prop :=
  ∀ Δ, closedB t 0 → envType Δ Γ → expType (substF Δ t) τ

-- compatibility lemmas

lemma semVar: ∀ Γ x τ, binds x τ Γ → semType Γ (.fvar x) τ := by
  intros Γ x τ bd Δ hcl henv; simp;
  rcases henv with ⟨_, h⟩;
  have ⟨v, hrv, semv⟩ := h τ x bd;
  exists v; rw [hrv]; simp; constructor; constructor; apply semv

lemma semApp: ∀ Γ f t τ1 τ2,
  semType Γ f (.arrow τ1 τ2) →
  semType Γ t τ1 →
  semType Γ (.app f t) τ2 := by
  intros Γ f t τ1 τ2 hsemf hsemt Δ hcl henv
  rcases hcl  with ⟨hclf, hclt⟩
  rcases hsemf Δ hclf henv with ⟨fv, hfv, clfv, semfv⟩
  rcases hsemt Δ hclt henv with ⟨tv, htv, cltv, semtv⟩
  unfold valType at semfv; cases fv <;> simp at semfv;
  case _ ft =>
  have ⟨v2, v2st, semv2⟩ := semfv tv semtv cltv
  exists v2; apply And.intro;
  . simp;
    apply stepnTrans; apply stepnApp1; assumption
    apply stepnTrans; apply stepnApp2; assumption
    have stbeta : step (ft.abs.app tv) (openSubst ft 0 tv) :=
      by apply step.st_beta; apply valTypeValue; assumption
    apply stepnTrans; apply stepn.stepn_multi; apply stepn.stepn_refl
    apply stbeta; apply v2st;
  . assumption

lemma semAbs: ∀ Γ t τ1 τ2,
  semType (τ1::Γ) (openSubst t 0 (.fvar Γ.length)) τ2 →
  closedF t Γ.length →
  semType Γ (.abs t) (.arrow τ1 τ2) := by
  intros Γ t τ1 τ2 hsemt hclosed Δ hcl henv
  exists (substF Δ (.abs t))
  apply And.intro
  . apply stepn.stepn_refl
  . simp at hcl; have hcl' := openClosed' t (Γ.length) 0 hcl
    apply And.intro
    . simp; apply substFClosedBComm _ _ _ (envTypeClosed Δ Γ henv) hcl
    . simp; intros v1 hv1 hclv1;
      unfold semType at hsemt;
      have henv' := envTypeExtend Δ Γ v1 τ1 henv hclv1 hv1
      have hsemt' := hsemt (v1::Δ) hcl' henv'
      simp at hsemt'; rcases hsemt' with ⟨vy, hyst, semvy⟩
      exists vy; apply And.intro
      . rw [<-henv.1] at hyst; rw [substFOpenComm] at hyst; assumption
        rw [henv.1]; assumption; apply envTypeClosed Δ Γ henv
      . assumption

-- fundamental property

lemma fundamental : ∀ Γ t τ, hasType Γ t τ → semType Γ t τ := by
  intros Γ t τ h; induction h
  case t_var => apply semVar; assumption
  case t_abs => apply semAbs <;> assumption
  case t_app => apply semApp <;> assumption

lemma hasTypeClosed : ∀ Γ t τ, hasType Γ t τ → closedB t 0 := by
  intros Γ t τ h; induction h <;> simp
  case t_abs => apply openClosed; assumption
  case t_app => apply And.intro <;> assumption

lemma substFMt: ∀ t, substF [] t = t := by
  intros t; induction t <;> simp
  assumption; apply And.intro <;> assumption

theorem safety : ∀ t τ, hasType [] t τ → expType t τ := by
  intros t τ h; have h' := fundamental _ _ _ h
  simp at h'; rcases h' (hasTypeClosed _ _ _ h) with ⟨v, hst, hval⟩
  simp; exists v; rw [substFMt] at hst;
  apply And.intro <;> assumption
