
-- STLC with full CBN
-- locally nameless where free variables are de Bruijn levels
-- small-step semantics and binary logical relations
-- contextual equivalence

import Mathlib.Data.Finset.Sort
import STLC.Env

namespace Smallstep_Equiv_CBN

inductive ty : Type
| bool : ty
| arrow : ty → ty → ty

inductive tm : Type
| fls : tm
| tru : tm
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
  | .fls | .tru => t1
  | .bvar x =>
    if x = n then t2
    -- XX: we still need this?
    -- else if n < x then .bvar (x - 1)
    else .bvar x
  | .fvar x => .fvar x
  | .abs t1 => .abs (openSubst t1 (n + 1) t2)
  | .app t11 t12 =>
    .app (openSubst t11 n t2) (openSubst t12 n t2)

@[simp]
def close (t1: tm) (n: ℕ) (m: ℕ) : tm :=
  match t1 with
  | .fls | .tru => t1
  | .bvar x => .bvar x
  | .fvar x => if x = n then (.bvar m) else t1
  | .abs t1 => .abs (close t1 n (m + 1))
  | .app t11 t12 =>
    .app (close t11 n m) (close t12 n m)

example : (tm.abs (close (.abs (.fvar 0)) 0 0)) = (.abs (.abs (.bvar 1))) := by simp

@[simp]
def substF (Δ: venv) (t: tm) : tm :=
  match t with
  | .fls | .tru => t
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
  | .fls | .tru => true
  | .bvar _ => true
  | .fvar x => x < n
  | .abs t1 => closedF t1 n
  | .app t11 t12 => closedF t11 n ∧ closedF t12 n

@[simp]
def closedB (t: tm) (n: ℕ) : Prop :=
  match t with
  | .fls | .tru => true
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
    . rw [if_neg hx]; simp at h; simp; omega
  case abs t ih =>
    apply ih n (m+1); simp at h; assumption
  case app t1 t2 ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2

lemma closedBOpenId: ∀ t1 t2 n,
  closedB t1 n -> openSubst t1 n t2 = t1 := by
  intros t1; induction t1 <;> intros t2 n h <;> simp
  case bvar x => intros hxn; simp at h; omega
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

lemma closedFInc: ∀ t n k, closedF t n -> closedF (openSubst t k (tm.fvar n)) (n + 1) := by
  intros t; induction t <;> intros n k hcl <;> simp
  case fvar x => simp at hcl; omega
  case bvar x =>
    by_cases hx: (x = k)
    . simp [hx];
    . rw [if_neg hx]; simp;
  case abs t ih => apply ih; simp at hcl; assumption
  case app t1 t2 ih1 ih2 =>
    apply And.intro
    . apply ih1; apply hcl.1
    . apply ih2; apply hcl.2

lemma substFOpenComm : ∀ t t1 Δ n, closedF t Δ.length →
  (∀ x t1, indexr x Δ = some t1 → closedB t1 0) →
  substF (t1::Δ) (openSubst t n (.fvar Δ.length)) =
  openSubst (substF Δ t) n t1 := by
  intros t t1 Δ n h; revert n; induction t <;> intros n hc <;> simp
  case bvar x =>
    by_cases hx: (x = n)
    . simp [hx]
    . rw [if_neg hx]; rw [if_neg hx]; simp
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
| fls : ∀ Γ, hasType Γ .fls .bool
| tru : ∀ Γ, hasType Γ .tru .bool
| var : ∀ Γ x τ, binds x τ Γ → hasType Γ (.fvar x) τ
| abs : ∀ Γ t τ₁ τ₂,
  hasType (τ₁::Γ) (openSubst t 0 (.fvar Γ.length)) τ₂ →
  closedF t Γ.length →
  hasType Γ (.abs t) (ty.arrow τ₁ τ₂)
| app : ∀ Γ t₁ t₂ τ₁ τ₂,
  hasType Γ t₁ (.arrow τ₁ τ₂) →
  hasType Γ t₂ τ₁ →
  hasType Γ (.app t₁ t₂) τ₂

inductive value : tm → Prop
| fls : value .fls
| tru : value .tru
| abs : ∀ t, value (.abs t)

inductive step : tm → tm → Prop
| beta : ∀ t1 t2,
  step (.app (.abs t1) t2) (openSubst t1 0 t2)
| app1 : ∀ t1 t1' t2,
  step t1 t1' →
  step (.app t1 t2) (.app t1' t2)
| app2 : ∀ t1 t2 t2',
  step t2 t2' →
  step (.app t1 t2) (.app t1 t2')
| lam : ∀ t1 t2,
  step t1 t2 →
  step (.abs t1) (.abs t2)

inductive stepn : tm → tm → Prop
| refl : ∀ t, stepn t t
| multi : ∀ t1 t2 t3, stepn t1 t2 → step t2 t3 → stepn t1 t3

lemma stepnApp1 : ∀ t1 t1' t2, stepn t1 t1' → stepn (.app t1 t2) (.app t1' t2) := by
  intros t1 t1' t2 h; induction h
  . constructor
  . case _ hstn hst ih => constructor; assumption; apply step.app1; assumption

lemma stepnApp2 : ∀ t1 t2 t2', value t1 → stepn t2 t2' → stepn (.app t1 t2) (.app t1 t2') := by
  intros t1 t2 t2' hv h; induction h
  . constructor
  . case _ hstn hst ih => apply stepn.multi; assumption; apply step.app2; assumption

lemma stepnTrans : ∀ t1 t2 t3, stepn t1 t2 → stepn t2 t3 → stepn t1 t3 := by
  intros t1 t2 t3 h1 h2; induction h2
  . assumption
  . case _ _ _ hstn hst ih =>
    apply stepn.multi; apply ih; assumption

-- valType is indexed by an tenv too

@[simp]
def valType (t1 : tm) (t2 : tm) (τ : ty) : Prop :=
  match t1, t2, τ with
  | .fls, .fls, .bool => true
  | .tru, .tru, .bool => true
  | (.abs t1), (.abs t2), .arrow τ1 τ2 =>
    ∀ v1 v2,
    valType v1 v2 τ1 → closedB v1 0 → closedB v2 0 →
    ∃ v3 v4,
    stepn (openSubst t1 0 v1) v3 ∧ closedB v3 0 ∧
    stepn (openSubst t2 0 v2) v4 ∧ closedB v4 0 ∧
    valType v3 v4 τ2
  | _, _, _ => false

lemma valTypeValue : ∀ t1 t2 τ, valType t1 t2 τ → value t1 ∧ value t2 := by
  intros t1 t2 τ h; cases t1 <;> cases t2 <;> try simp at h
  . apply And.intro <;> constructor
  . apply And.intro <;> constructor
  . next t1 t2 => apply And.intro <;> apply value.abs

@[simp]
def expType (t1 : tm) (t2 : tm) (τ : ty) : Prop :=
  ∃ v1 v2, stepn t1 v1 ∧ stepn t2 v2 ∧
           closedB v1 0 ∧ closedB v2 0 ∧
           valType v1 v2 τ

@[simp]
def envType (Δ1 : venv) (Δ2 : venv) (Γ : tenv) : Prop :=
  Δ1.length = Γ.length ∧
  Δ2.length = Γ.length ∧
  ∀ τ x, binds x τ Γ →
  ∃ v1 v2,
  indexr x Δ1 = some v1 ∧ closedB v1 0 ∧
  indexr x Δ2 = some v2 ∧ closedB v2 0 ∧
  valType v1 v2 τ

lemma envTypeMt : envType [] [] [] := by simp

lemma envTypeExtend : ∀ Δ1 Δ2 Γ v1 v2 τ,
  envType Δ1 Δ2 Γ →
  closedB v1 0 → closedB v2 0 →
  valType v1 v2 τ →
  envType (v1::Δ1) (v2::Δ2) (τ::Γ) := by
  intros Δ1 Δ2 Γ v1 v2 τ henv hclv1 hclv2 hv12
  constructor; simp; apply henv.1
  constructor; simp; apply henv.2.1
  intros τ' x hbd; rcases henv with ⟨hlen1, hlen2, h⟩
  by_cases hx: (x = Δ1.length)
  . simp [hx]; constructor; assumption; simp [hlen1, hlen2]
    constructor; assumption; simp at hbd; simp [hx, hlen1] at hbd
    rw [<- hbd]; assumption
  . simp at hbd; rw [<-hlen1, if_neg hx] at hbd;
    simp; rw [if_neg hx]; rw [hlen2, <-hlen1, if_neg hx]
    specialize h τ' x hbd; rcases h with ⟨v1, v2, h⟩
    exists v1; constructor; exact h.1; constructor; exact h.2.1
    exists v2; exact h.2.2

lemma envTypeClosed : ∀ Δ1 Δ2 Γ, envType Δ1 Δ2 Γ →
  (∀ x t1, indexr x Δ1 = some t1 → closedB t1 0) ∧
  (∀ x t1, indexr x Δ2 = some t1 → closedB t1 0) := by
  intros Δ1 Δ2 Γ henv; rcases henv with ⟨hlen1, hlen2, h⟩
  apply And.intro
  . intros x t1 hidx;
    have hx : (x < Δ1.length) := by apply indexrSome'; exists t1
    rw [hlen1] at hx; have hidx' := indexrSome Γ x hx
    rcases hidx' with ⟨τ, hidx'⟩;
    have ⟨v1, v2, hidxv1, hclv1, hidxv2, hclv2, hval⟩  := h τ x hidx'
    rw [hidx] at hidxv1; cases hidxv1; assumption
  . intros x t1 hidx;
    have hx : (x < Δ2.length) := by apply indexrSome'; exists t1
    rw [hlen2] at hx; have hidx' := indexrSome Γ x hx
    rcases hidx' with ⟨τ, hidx'⟩;
    have ⟨v1, v2, hidxv1, hclv1, hidxv2, hclv2, hval⟩  := h τ x hidx'
    rw [hidx] at hidxv2; cases hidxv2; assumption

@[simp]
def wf (t: tm) (Γ: tenv) := closedB t 0 ∧ closedF t (Γ.length)

@[simp]
def semType (Γ : tenv) (t1 t2 : tm) (τ : ty) : Prop :=
  ∀ Δ1 Δ2,
  wf t1 Γ → wf t2 Γ →
  envType Δ1 Δ2 Γ →
  expType (substF Δ1 t1) (substF Δ2 t2) τ

lemma semTrue : ∀ Γ, semType Γ .tru .tru .bool := by
  intros Γ Δ1 Δ2 h _ _ ; exists (.tru); exists (.tru); simp; apply stepn.refl

lemma semFalse : ∀ Γ, semType Γ .fls .fls .bool := by
  intros Γ Δ1 Δ2 h _ _; exists (.fls); exists (.fls); simp; apply stepn.refl

lemma semVar : ∀ Γ x τ, binds x τ Γ → semType Γ (.fvar x) (.fvar x) τ := by
  intros Γ x τ hbd Δ1 Δ2 _ _ henv
  rcases henv with ⟨_, _, h⟩
  have ⟨v1, v2, idx1, cl1, idx2, cl2, semv⟩ := h τ x hbd
  exists v1; exists v2; simp [idx1, idx2]
  exact ⟨stepn.refl v1, stepn.refl v2, cl1, cl2, semv⟩

lemma semApp : ∀ Γ f1 f2 t1 t2 τ1 τ2,
  semType Γ f1 f2 (.arrow τ1 τ2) →
  semType Γ t1 t2 τ1 →
  semType Γ (.app f1 t1) (.app f2 t2) τ2 := by
  intros Γ f1 f2 t1 t2 τ1 τ2 hsemf hsemt Δ1 Δ2 hwf1 hwf2 henv
  simp at hwf1; simp at hwf2
  unfold semType at hsemf hsemt
  rcases hsemf Δ1 Δ2 ⟨hwf1.1.1, hwf1.2.1⟩ ⟨hwf2.1.1, hwf2.2.1⟩ henv with ⟨v1, v2, hstn1, hstn2, hcl1, hcl2, hv12⟩
  rcases hsemt Δ1 Δ2 ⟨hwf1.1.2, hwf1.2.2⟩ ⟨hwf2.1.2, hwf2.2.2⟩ henv with ⟨v3, v4, hstn3, hstn4, hcl3, hcl4, hv34⟩
  cases v1 <;> cases v2 <;> try simp at hv12
  case _ f1t f2t =>
  have ⟨v5, hst5, hcl5, v6, hst6, hcl6, hv56⟩ := hv12 v3 v4 hv34 hcl3 hcl4
  exists v5; exists v6; constructor
  apply stepnTrans; apply stepnApp1; assumption
  apply stepnTrans; apply stepnApp2; constructor; assumption
  have stbeta : step (f1t.abs.app v3) (openSubst f1t 0 v3) :=
    by apply step.beta; exact (valTypeValue _ _ _ hv34).1
  apply stepnTrans; apply stepn.multi; apply stepn.refl
  apply stbeta; apply hst5;
  --
  constructor
  apply stepnTrans; apply stepnApp1; assumption
  apply stepnTrans; apply stepnApp2; constructor; assumption
  have stbeta : step (f2t.abs.app v4) (openSubst f2t 0 v4) :=
    by apply step.beta; exact (valTypeValue _ _ _ hv34).2
  apply stepnTrans; apply stepn.multi; apply stepn.refl
  apply stbeta; apply hst6;
  exact ⟨hcl5, hcl6, hv56⟩

lemma lenInc: ∀ {A} x (L : List A), L.length + 1 = (x::L).length := by intros _ L x; simp

lemma semAbs : ∀ Γ t1 t2 τ1 τ2,
  semType (τ1::Γ) (openSubst t1 0 (.fvar Γ.length)) (openSubst t2 0 (.fvar Γ.length)) τ2 →
  semType Γ (.abs t1) (.abs t2) (.arrow τ1 τ2) :=
by
  intros Γ t1 t2 τ1 τ2 hsem Δ1 Δ2 hwf1 hwf2 henv
  exists (substF Δ1 (.abs t1)); exists (substF Δ2 (.abs t2))
  constructor; apply stepn.refl
  constructor; apply stepn.refl
  simp at hwf1; simp at hwf2
  have hclb1' := openClosed' t1 (Γ.length) 0 hwf1.1
  have hclb2' := openClosed' t2 (Γ.length) 0 hwf2.1
  have envcl := envTypeClosed Δ1 Δ2 Γ henv
  constructor; apply substFClosedBComm _ _ _ envcl.1 hwf1.1
  constructor; apply substFClosedBComm _ _ _ envcl.2 hwf2.1
  simp; intros v1 v2 hval12 hclv1 hclv2;
  have henv' := envTypeExtend Δ1 Δ2 Γ v1 v2 τ1 henv hclv1 hclv2 hval12
  have clf1' := closedFInc _ _ 0 hwf1.2;
  have clf2' := closedFInc _ _ 0 hwf2.2;
  have hsem' := hsem (v1::Δ1) (v2::Δ2) ⟨hclb1', clf1'⟩ ⟨hclb2', clf2'⟩ henv'
  rcases hsem' with ⟨vr1, vr2, hstr1, hstr2, hclvr1, hclvr2, semvr⟩
  rw [<-henv.1] at hstr1; rw [<-henv.2.1] at hstr2
  rw [substFOpenComm] at hstr1; rw [substFOpenComm] at hstr2
  exists vr1; constructor; assumption; constructor; assumption
  exists vr2; rw [henv.2.1]; exact hwf2.2; exact envcl.2; rw [henv.1]; exact hwf1.2
  exact envcl.1

theorem fundamental : ∀ Γ t τ,
  hasType Γ t τ → semType Γ t t τ := by
  intros Γ t τ h; induction h
  case fls => apply semFalse
  case tru => apply semTrue
  case var => apply semVar; assumption
  case abs => apply semAbs; assumption
  case app => apply semApp <;> assumption

lemma hasTypeClosedB : ∀ Γ t τ, hasType Γ t τ → closedB t 0 := by
  intros Γ t τ h; induction h <;> simp
  case abs => apply openClosed; assumption
  case app => apply And.intro <;> assumption

lemma substFMt: ∀ t, substF [] t = t := by
  intros t; induction t <;> simp
  assumption; apply And.intro <;> assumption

lemma hasTypeClosedF : ∀ t τ, hasType [] t τ → closedF t 0 := by
  intros t τ h; revert τ; induction t <;> intros τ h <;> simp
  . case fvar x => cases h; next bd => simp at bd
  . case abs t ih => cases h; assumption
  . case app t1 t2 ih1 ih2 =>
    cases h; apply And.intro
    . apply ih1; assumption
    . apply ih2; assumption

theorem safety : ∀ t τ, hasType [] t τ → expType t t τ := by
  intros t τ h; have h' := fundamental _ _ _ h
  have b := hasTypeClosedB [] t τ h
  have f := hasTypeClosedF t τ h
  rcases h' [] [] ⟨b, f⟩ ⟨b, f⟩ envTypeMt with ⟨v1, v2, hst1, hst2, hclb1, hclb2, hval⟩; simp
  exists v1; rw [substFMt] at hst1; constructor; assumption
  exists v2; rw [substFMt] at hst2; constructor; assumption
  exact ⟨hclb1, hclb2, hval⟩

inductive ctxType : (tm → tm) → tenv → ty → tenv → ty → Prop
| root : ∀ Γ τ, ctxType id Γ τ Γ τ
| app1 : ∀ Γ τ1 τ2 t2,
  hasType Γ t2 τ1 →
  ctxType (λ t1 => .app t1 t2) Γ (.arrow τ1 τ2) Γ τ2
| app2 : ∀ Γ τ1 τ2 t1,
  hasType Γ t1 (.arrow τ1 τ2) →
  ctxType (λ t2 => .app t1 t2) Γ τ1 Γ τ2
| abs : ∀ Γ τ1 τ2,
  -- t is an opened term, referring to a free variable (.fvar Γ.length)
  ctxType (λ t => .abs (close t Γ.length 0)) (τ1::Γ) τ2 Γ (.arrow τ1 τ2)

def closedCtx (C: tm → tm) :=
  ∀ Γ1 τ1 Γ2 τ2, ctxType C Γ1 τ1 Γ2 τ2 → ∀ t, wf t Γ1 → wf (C t) Γ2

lemma openCloseId : ∀ t n k, closedB t k → (openSubst (close t n k) k (tm.fvar n)) = t := by
  intros t; induction t <;> intros n k hcl <;> simp;
  . case bvar x => simp at hcl; omega
  . case fvar x => by_cases hx: (x = n); simp [hx]; simp [if_neg hx]
  . case abs t ih => apply ih; exact hcl
  . case app t1 t2 ih1 ih2 =>
    simp at hcl; apply And.intro
    . apply ih1; exact hcl.1
    . apply ih2; exact hcl.2

theorem congruence : ∀ C Γ1 τ1 Γ2 τ2,
  ctxType C Γ1 τ1 Γ2 τ2 →
  ∀ t1 t2,
  closedB t1 0 → closedB t2 0 →
  semType Γ1 t1 t2 τ1 → semType Γ2 (C t1) (C t2) τ2 :=
by
  intros C Γ1 τ1 Γ2 τ2 hctx
  induction hctx <;> intros t1 t2 hcl1 hcl2 hsem
  . case root _ _ => apply hsem
  . case app1 Γ τ1' τ2' t2' htyt2' =>
    apply semApp; apply hsem; apply fundamental; assumption
  . case app2 Γ τ1' τ2' t1' htyt1' =>
    apply semApp; apply fundamental; assumption; apply hsem
  . case abs Γ τ1' τ2' =>
    apply semAbs; rw [openCloseId]; rw [openCloseId]
    assumption; assumption; assumption

theorem adaquacy : ∀ t1 t2 τ,
  wf t1 [] → wf t2 [] →
  semType [] t1 t2 τ →
  ((∃ v1, stepn t1 v1 ∧ value v1) ↔ (∃ v2, stepn t2 v2 ∧ value v2)) := by
  intros t1 t2 τ wf1 wf2 hsem;
  specialize hsem [] [] wf1 wf2 envTypeMt
  rcases hsem with ⟨v1, v2, hst1, hst2, hcl1, hcl2, hv12⟩
  apply Iff.intro
  . intros h1; exists v2; rw [substFMt] at hst2
    exact ⟨hst2, (valTypeValue _ _ _ hv12).2⟩
  . intros h1; exists v1; rw [substFMt] at hst1
    exact ⟨hst1, (valTypeValue _ _ _ hv12).1⟩

def ctxEquiv Γ t1 t2 τ :=
  hasType Γ t1 τ →
  hasType Γ t2 τ →
  ∀ C, ctxType C Γ τ [] .bool → closedCtx C →
  ((∃ v1, stepn (C t1) v1 ∧ value v1) ↔ (∃ v2, stepn (C t2) v2 ∧ value v2))

theorem soundness : ∀ Γ t1 t2 τ,
  wf t1 Γ → wf t2 Γ →
  semType Γ t1 t2 τ → ctxEquiv Γ t1 t2 τ := by
  intros Γ t1 t2 τ hwf1 hwf2 hsem htyt1 htyt2 C hctx hctxcl
  have hcs := congruence _ _ _ _ _ hctx _ _ hwf1.1 hwf2.1 hsem
  have hc1 := (hctxcl _ _ _ _ hctx _ hwf1)
  have hc2 := (hctxcl _ _ _ _ hctx _ hwf2)
  apply adaquacy; exact hc1; exact hc2; apply hcs

theorem soundness' : ∀ Γ t1 t2 τ,
  semType Γ t1 t2 τ →
  wf t1 Γ → wf t2 Γ →
  hasType Γ t1 τ → hasType Γ t2 τ →
  ∀ C, ctxType C Γ τ [] .bool → closedCtx C →
  ∃ v, stepn (C t1) v ∧ stepn (C t2) v ∧ value v := by
  intros Γ t1 t2 τ hsem hwf1 hwf2 hty1 hty2 C hctx hctxcl
  have hcs := congruence _ _ _ _ _ hctx _ _ hwf1.1 hwf2.1 hsem
  specialize hcs [] [] (hctxcl _ _ _ _ hctx _ hwf1) (hctxcl _ _ _ _ hctx _ hwf2) envTypeMt
  rw [substFMt] at hcs; rw [substFMt] at hcs
  rcases hcs with ⟨v1, v2, hst1, hst2, hcl1, hcl2, hv12⟩
  cases v1 <;> cases v2 <;> try simp at hv12
  exists .fls; constructor; assumption; constructor; assumption; constructor
  exists .tru; constructor; assumption; constructor; assumption; constructor
