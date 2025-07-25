-- STLC with full beta-reduction
-- locally nameless where free variables are de Bruijn levels
-- small-step semantics and unary logical relation
-- following Kripke-Style Logical Relations for Normalization, Robert Harper

-- XXX: UNFINISHED

import Mathlib.Data.Finset.Sort
import STLC.Env

namespace Smallstep_Equiv_Beta

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
    else if n < x then .bvar (x - 1)
    else .bvar x
  | .fvar x => .fvar x
  | .abs t1 => .abs (openSubst t1 (n + 1) t2)
  | .app t11 t12 =>
    .app (openSubst t11 n t2) (openSubst t12 n t2)

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
    apply ih n (m+1); simp at h; assumption
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

lemma closedFInc: ∀ t n k, closedF t n -> closedF (openSubst t k (tm.fvar n)) (n + 1) := by
  intros t; induction t <;> intros n k hcl <;> simp
  case fvar x => simp at hcl; omega
  case bvar x =>
    by_cases hx: (x = k)
    . simp [hx];
    . rw [if_neg hx];
      by_cases hx': (k < x)
      . simp [hx']
      . rw [if_neg hx']; simp
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

lemma stepnApp2 : ∀ t1 t2 t2', stepn t2 t2' → stepn (.app t1 t2) (.app t1 t2') := by
  intros t1 t2 t2' h; induction h
  . constructor
  . case _ hstn hst ih => apply stepn.multi; assumption; apply step.app2; assumption

lemma stepnLam : ∀ t1 t2, stepn t1 t2 → stepn (.abs t1) (.abs t2) := by
  intros t1 t2 h; induction h
  . constructor
  . case _ hstn hst ih => apply stepn.multi; assumption; apply step.lam; assumption

lemma stepnTrans : ∀ t1 t2 t3, stepn t1 t2 → stepn t2 t3 → stepn t1 t3 := by
  intros t1 t2 t3 h1 h2; induction h2
  . assumption
  . case _ _ _ hstn hst ih =>
    apply stepn.multi; apply ih; assumption

lemma stepn.multi' : ∀ t1 t2 t3, step t1 t2 → stepn t2 t3 → stepn t1 t3 := by
  intros t1 t2 t3 st1 st2
  have st3 : stepn t1 t1 := by constructor
  have st4 : stepn t1 t2 := by apply stepn.multi; assumption; apply st1
  apply stepnTrans; assumption; assumption

def extend (Γ1 Γ2 : tenv) : Prop :=
  ∀ x τ, hasType Γ1 (.fvar x) τ → hasType Γ2 (.fvar x) τ

notation:60 a:65 "≤" b:65 => extend a b

lemma extendRefl : ∀ Γ, Γ ≤ Γ := by intros Γ x τ hty; assumption

lemma extend1 : ∀ τ Γ, Γ ≤ (τ :: Γ) := by
  intros τ Γ x τ hty
  rcases hty; case var τ1 hbd =>
    by_cases hx: (x >= Γ.length);
    . simp at hbd; rw [indexrNone] at hbd; cases hbd; omega
    . constructor; simp; aesop

lemma extendTrans : ∀ Γ1 Γ2 Γ3,
  Γ1 ≤ Γ2 → Γ2 ≤ Γ3 → Γ1 ≤ Γ3 := by
  intros Γ1 Γ2 Γ3 hE1 hE2 x τ hT;
  apply hE2; apply hE1; assumption

@[simp]
def βnorm (t: tm) : Prop := ¬ ∃ t', step t t'

@[simp]
def normalizable (t: tm) : Prop := ∃ t', stepn t t' ∧ βnorm t'

-- hereditary normalization
@[simp]
def HN (Γ: tenv) (t: tm) (τ: ty): Prop :=
  match τ with
  | .bool => normalizable t
  | .arrow τ1 τ2 =>
    ∀ Γ' t1, Γ ≤ Γ' → closedB t1 0 → HN Γ' t1 τ1 → HN Γ' (.app t t1) τ2

lemma monotonicity : ∀ Γ1 Γ2 t τ, Γ2 ≤ Γ1 → HN Γ2 t τ → HN Γ1 t τ := by
  intros Γ1 Γ2 t τ hE hv; induction τ
  case bool => exact hv
  case arrow τ1 τ2 ih1 ih2 =>
    intros Γ' t1 hE' hvalt1
    apply hv; apply extendTrans; apply hE; apply hE'; assumption

lemma headExpansion : ∀ Γ t1 t2 τ, step t1 t2 → HN Γ t2 τ → HN Γ t1 τ := by
  intros Γ t1 t2 τ hst hv
  induction τ generalizing Γ t1 t2
  case bool =>
    simp at hv; simp; rcases hv with ⟨v, hstn, hnorm⟩
    exists v; constructor; apply stepn.multi'; apply hst
    apply hstn; apply hnorm
  case arrow τ1 τ2 ih1 ih2 =>
    intro Γ' t1' hE hvalt1'
    have hst' : step (t1.app t1') (t2.app t1') := by constructor; assumption
    aesop

@[simp]
def envType (Δ : tenv) (Γ : tenv) (γ : venv) : Prop :=
  Γ.length = γ.length ∧
  ∀ τ x, binds x τ Γ →
  ∃ v, indexr x γ = some v ∧ closedB v 0 ∧ HN Δ v τ

lemma monoEnv : ∀ Δ1 Δ2 Γ γ, Δ2 ≤ Δ1 →
  envType Δ2 Γ γ → envType Δ1 Γ γ := by
  intros Δ1 Δ2 Γ γ hE henv; rcases henv with ⟨hlen, h⟩
  constructor; assumption; intros τ x hbd
  specialize h τ x hbd
  rcases h with ⟨v, hidx, hcl, hv⟩
  exists v; constructor; assumption; constructor; assumption
  apply monotonicity; assumption; assumption

lemma envTypeMt : ∀ Δ, envType Δ [] [] := by simp

lemma envTypeExtend : ∀ Δ Γ γ v τ,
  envType Δ Γ γ → closedB v 0 → HN Δ v τ → envType Δ (τ::Γ) (v::γ) := by
  intros Δ Γ γ v τ henv hcl hv; simp; simp at henv
  apply And.intro
  . apply henv.1
  . intros τ1 x bd; rcases henv with ⟨hlen, h⟩
    by_cases hx: (x = Γ.length)
    . rw [hx] at bd; simp at bd
      rw [hx, hlen]; simp [hx]; rw [<-bd]; apply And.intro <;> assumption
    . rw [if_neg hx] at bd; rw [<-hlen]; rw [if_neg hx]
      specialize h τ1 x bd; rcases h with ⟨v, hidx, hclv, hv⟩; exists v

lemma envTypeClosed : ∀ Δ Γ γ, envType Δ Γ γ →
  (∀ x t1, indexr x γ = some t1 → closedB t1 0) := by
  intros Δ Γ γ henv; rcases henv with ⟨hlen, h⟩
  intros x t1 hidx;
  have hx : (x < γ.length) := by apply indexrSome'; exists t1
  rw [<-hlen] at hx; have hidx' := indexrSome Γ x hx
  rcases hidx' with ⟨τ, hidx'⟩;
  have ⟨t2, hidx'', hval⟩  := h τ x hidx'
  rcases hval with ⟨hcl, _⟩; rw [hidx] at hidx''; cases hidx''; assumption

@[simp]
def semType (Γ : tenv) (t : tm) (τ : ty) : Prop :=
  ∀ Δ γ, closedB t 0 → envType Δ Γ γ → HN Δ (substF γ t) τ

lemma semFls: ∀ Γ, semType Γ .fls .bool := by
  intros Γ Δ γ hcl henv; simp; rcases henv with ⟨hlen, h⟩
  exists .fls; constructor; apply stepn.refl; intros x f; cases f

lemma semTru: ∀ Γ, semType Γ .tru .bool := by
  intros Γ Δ γ hcl henv; simp; rcases henv with ⟨hlen, h⟩
  exists .tru; constructor; apply stepn.refl; intros x f; cases f

lemma semVar: ∀ Γ x τ, binds x τ Γ → semType Γ (.fvar x) τ := by
  intros Γ x τ bd Δ γ hcl henv; simp
  rcases henv with ⟨hlen, henv⟩
  rcases henv _ _ bd with ⟨w, h⟩
  simp [h.1]; exact h.2.2

lemma semApp: ∀ Γ f t τ1 τ2,
  semType Γ f (.arrow τ1 τ2) →
  semType Γ t τ1 →
  semType Γ (.app f t) τ2 := by
  intros Γ f t τ1 τ2 hsemf hsemt Δ γ hcl henv
  rcases hcl  with ⟨hclf, hclt⟩
  specialize hsemf Δ γ hclf henv
  specialize hsemt Δ γ hclt henv
  have he : extend Δ Δ := by apply extendRefl
  have hcl : closedB (substF γ t) 0 := by
    apply substFClosedBComm; apply envTypeClosed Δ Γ γ henv; assumption
  specialize hsemf Δ (substF γ t) he hcl hsemt
  simp; assumption

lemma semAbs: ∀ Γ t τ1 τ2,
  semType (τ1::Γ) (openSubst t 0 (.fvar Γ.length)) τ2 →
  closedF t Γ.length →
  semType Γ (.abs t) (.arrow τ1 τ2) := by
  intros Γ t τ1 τ2 hsemt hclosed Δ γ hcl henv
  intros Γ' t1 he hclt1 hvalt1; simp; simp at hcl
  have hcl' := openClosed' t (Γ.length) 0 hcl
  have henv' : envType Γ' Γ γ := by apply monoEnv <;> assumption
  have henv'' : envType Γ' (τ1::Γ) (t1::γ) := by apply envTypeExtend <;> assumption
  specialize hsemt Γ' (t1::γ) hcl' henv''
  rw [henv.1, substFOpenComm] at hsemt
  have st : step ((substF γ t).abs.app t1) (openSubst (substF γ t) 0 t1) := by apply step.beta
  apply headExpansion; assumption; assumption
  rw [<-henv.1]; assumption
  apply envTypeClosed Δ Γ γ henv

lemma fundamental : ∀ Γ t τ,
  hasType Γ t τ → semType Γ t τ := by
  intros Γ t τ hty
  induction hty
  case fls => apply semFls
  case tru => apply semTru
  case var x τ hbd => apply semVar; assumption
  case abs τ1 τ2 t ih hcl => apply semAbs; assumption; assumption
  case app t1 t2 τ1 τ2 ih1 ih2 =>
    apply semApp; assumption; assumption

-- neutral normality

inductive neutral : tm → Prop
| var : ∀ x, neutral (.fvar x)
| app : ∀ t1 t2, neutral t1 → normalizable t2 → neutral (.app t1 t2)

lemma absBetaNorm : ∀ t1, (∀ t2, ¬step t1.abs t2) → ∀ t3, ¬step t1 t3 := by
  intros t1 st1 t3 st2;
  have st3 : step t1.abs t3.abs := by apply step.lam; assumption
  specialize st1 t3.abs
  exact st1 st3

lemma βnormApp : ∀ t1 t2, βnorm (.app t1 t2) → βnorm t1 ∧ βnorm t2 := by
  intros t1 t2 h; simp at *; constructor
  intros x st; have h' := step.app1 t1 x t2 st; aesop
  intros x st; have h' := step.app2 t1 t2 x st; aesop

lemma stepnVar : ∀ x t, stepn (.fvar x) t → t = .fvar x := by
  intros x t hstepn; induction hstepn
  . simp
  . expose_names; rw [a_ih] at h_1; cases h_1

/--
lemma stepNeutral : ∀ t1 t2, stepn t1 t2 → neutral t1 →
  (∃ x, t2 = .fvar x) ∨ (∃ t3 t4, t2 = .app t3 t4) := by
  intros t1 t2 hstepn hneu
  cases hneu
  . expose_names; apply stepnVar at hstepn; aesop
  . expose_names; right;
--/

lemma βnormNormalizable : ∀ t, βnorm t → normalizable t := by
  intros t h; induction t <;> simp
  . exists .fls; constructor; apply stepn.refl; intros x st; cases st
  . exists .tru; constructor; apply stepn.refl; intros x st; cases st
  . expose_names; exists (.bvar a); constructor; apply stepn.refl; intros x st; cases st
  . expose_names; exists (.fvar a); constructor; apply stepn.refl; intros x st; cases st
  . expose_names; exists (.abs a); constructor; apply stepn.refl; intros x st; aesop
  . expose_names; exists (.app a a_1); constructor; apply stepn.refl; intros x st; aesop

lemma betaNormVarNeu : ∀ x, βnorm (.fvar x) → neutral (.fvar x) := by
  intros x h; constructor

/--
lemma betaNormAppNeu : ∀ t1 t2, βnorm (.app t1 t2) → neutral (.app t1 t2) := by
  intros t1 t2 h1
  have nm : normalizable (.app t1 t2) := by apply βnormNormalizable; assumption
  apply βnormApp at h1; rcases h1 with ⟨h2, h3⟩
  constructor;
  apply βnormNormalizable; assumption

lemma stepNeutral : ∀ t1, neutral t1 → ∀ t2, stepn t1 t2 →
  ¬ (∃ x, t2 = .abs x) := by
  intros t1 hneu
  induction hneu
  . sorry
  . expose_names;
-/


lemma stepPreservesNeutral : ∀ t1 t2, step t1 t2 → neutral t1 → neutral t2 := by
  intros t1 t2 hst hneu
  induction hst
  . case beta t3 t4 => cases hneu; expose_names; cases h
  . case app1 t3 t4 t5 hst ih =>
    cases hneu; constructor; apply ih; assumption; assumption
  . case app2 t3 t4 t5 hst ih =>
    cases hneu; constructor; assumption; expose_names;
    sorry
  . case lam t3 t4 hst ih => cases hneu

lemma stepnPreservesNeutral : ∀ t1 t2, stepn t1 t2 → neutral t1 → neutral t2 := by
  intros t1 t2 hstepn hneu
  induction hstepn
  . assumption
  . case multi t2 t3 t1st t3st t4ne =>
    apply stepPreservesNeutral; assumption; apply t4ne

/--
lemma normalizableApp : ∀ t1 t2, neutral t1 → normalizable t1 → normalizable t2 →
  normalizable (.app t1 t2) := by
  intros t1 t2 hne1 hnm1 hnm2
  rcases hnm1 with ⟨t1', hstn1, hnorm1⟩
  rcases hnm2 with ⟨t2', hstn2, hnorm2⟩
  exists (t1'.app t2'); constructor
  apply stepnTrans; apply stepnApp1; assumption
  apply stepnApp2; assumption
  intro st; rcases st with ⟨x, hst⟩
  have hst' := hst
  induction hne1 generalizing t1'
  . sorry
  . expose_names;
-/

lemma neutralNormalizable : ∀ t, neutral t → normalizable t := by
  intros t h; induction t <;> try cases h
  case var x =>
    exists (.fvar x); constructor; apply stepn.refl; simp; intros x st; cases st
  case app t1 t2 ih1 ih2 t1ne t2nm =>
    rcases (ih1 t1ne) with ⟨t1', hstn1, hnorm1⟩
    rcases t2nm with ⟨t2', hstn2, hnorm2⟩
    simp; exists (t1'.app t2'); constructor
    apply stepnTrans; apply stepnApp1; assumption
    apply stepnApp2; assumption
    intros x st;
    have t1'ne : neutral t1' := by
      apply stepnPreservesNeutral; assumption; assumption
    cases st; cases t1'ne; aesop; aesop

/---
  induction h
  case var x => simp; sorry
  case app t1 t2 t1ne t2nm t1nm =>
    rcases t1nm with ⟨t1', hstn1, hnorm1⟩
    rcases t2nm with ⟨t2', hstn2, hnorm2⟩
    simp; exists (t1'.app t2'); constructor
    apply stepnTrans; apply stepnApp1; assumption
    apply stepnApp2; assumption;
    -- t1' is neutral too
    have t1'ne : neutral t1' := by apply stepPreservesNeutral; assumption; assumption; assumption
    match t1'ne with
    | neutral.var x =>
      intros x st; cases st <;> expose_names; cases h
      unfold βnorm at hnorm2; aesop
    | neutral.app t1'' t2'' t1ne' t2nm' =>
      intros x st; cases st <;> expose_names;
      unfold βnorm at hnorm1; aesop
      unfold βnorm at hnorm2; aesop
--/

lemma hasTypeClosed : ∀ Γ t τ, hasType Γ t τ → closedB t 0 := by
  intros Γ t τ h; induction h <;> simp
  case abs => apply openClosed; assumption
  case app => apply And.intro <;> assumption

@[simp]
def mkIdSubst (Γ : tenv) : venv :=
  match Γ with
  | [] => []
  | _ :: Γ' => (.fvar Γ'.length) :: mkIdSubst Γ'

example: mkIdSubst [ty.bool, ty.bool] = [.fvar 1, .fvar 0] := by simp

lemma semVar' : ∀ Γ x τ, binds x τ Γ → HN Γ (.fvar x) τ := by
  intros Γ x τ bd;
  apply semVar at bd; unfold semType at bd;
  specialize bd Γ

lemma idSubstEnvType : ∀ Γ, envType Γ Γ (mkIdSubst Γ) := by
  intros Γ;
  constructor; sorry
  intros τ x bd; exists (.fvar x)
  constructor; sorry
  constructor; constructor; apply semVar'; assumption


/--
lemma pasDeDeux' : ∀ Γ τ,
  ((∀ t1, hasType Γ t1 τ → neutral t1 → HN Γ t1 τ) <->
   (∀ t2, hasType Γ t2 τ → HN Γ t2 τ → normalizable t2)) := by
  intros Γ τ; induction τ generalizing Γ
  constructor
  . intros h1 t hty hhn; assumption
  . intros h1 t hty hne;

  constructor
  . case arrow τ1 τ2 ih1 ih2 =>
    intros h1 t hty hhn; sorry
  . case arrow τ1 τ2 ih1 ih2 =>
    intros h1 t hty heu;
    unfold HN; intros Γ' t1 ext cl hnt1'
    sorry
--/


lemma pasDeDeux : ∀ Γ τ t1 t2, hasType Γ t1 τ → hasType Γ t2 τ →
  (neutral t1 → HN Γ t1 τ) ∧ (HN Γ t2 τ → normalizable t2) := by
  intros Γ τ t1 t2 hty1 hty2
  induction τ generalizing Γ t1 t2
  case bool =>
    constructor
    . intros hnt; have hty1' := hty1
      apply fundamental at hty1';
      unfold semType at hty1'
      have hn := hty1' Γ (mkIdSubst Γ) (hasTypeClosed _ _ _ hty1) (idSubstEnvType _)
      sorry
      --apply neutralNormalizable; assumption
    . intros hhn; assumption
  case arrow τ1 τ2 ih1 ih2 =>
    constructor
    . intros t1ne; unfold HN; intros Γ' t1' ext cl hnt1'
      have t1'nm : normalizable t1' := by
        specialize ih1 Γ' t1' t1' sorry sorry
        aesop
      have neapp : neutral (.app t1 t1') := by
        constructor; assumption; assumption
      specialize ih2 Γ' (t1.app t1') (t1.app t1') sorry sorry
      aesop
    . intros t2hn; unfold HN at t2hn;
      set Γ' := (τ1::Γ)
      have ext : Γ ≤ Γ' := by sorry


theorem normalization : ∀ Γ t τ, hasType Γ t τ → βnorm t := by
  intros Γ t τ hty
  have hsem := fundamental Γ t τ hty
  have cl := hasTypeClosed Γ t τ hty
  specialize hsem Γ sorry cl sorry
  have hv' := pasDeDeux Γ τ t t hty hty
  apply hv'.2; assumption

end Smallstep_Equiv_Beta
