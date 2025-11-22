-- STLC
-- locally nameless where free variables are de Bruijn levels
-- first-order reference store
-- call-by-value small-step semantics and binary logical relations
-- contextual equivalence

import Mathlib.Data.Finset.Sort
import STLC.Env

namespace Smallstep_Ref_Equiv

inductive ty : Type
| bool : ty
| ref : ty → ty
| arrow : ty → ty → ty

inductive tm : Type
| bool : Bool → tm
| bvar : ℕ → tm
| fvar : ℕ → tm
| abs : tm → tm
| app : tm → tm → tm
| loc : ℕ → tm
| ref : tm → tm
| deref : tm → tm
| assign : tm → tm → tm

abbrev tenv := List ty
abbrev venv := List tm

-- combine open and subst: t1[n ↦ t2]
@[simp]
def openSubst (t1: tm) (n: ℕ) (t2: tm) : tm :=
  match t1 with
  | .bool b => .bool b
  | .bvar x =>
    if x = n then t2
    -- else if n < x then .bvar (x - 1)
    else .bvar x
  | .fvar x => .fvar x
  | .abs t1 => .abs (openSubst t1 (n + 1) t2)
  | .app t11 t12 =>
    .app (openSubst t11 n t2) (openSubst t12 n t2)
  | .loc x => .loc x
  | .ref t1 => .ref (openSubst t1 n t2)
  | .deref t1 => .deref (openSubst t1 n t2)
  | .assign t11 t12 => .assign (openSubst t11 n t2) (openSubst t12 n t2)

@[simp]
def close (t1: tm) (n: ℕ) (m: ℕ) : tm :=
  match t1 with
  | .bool b => .bool b
  | .bvar x => .bvar x
  | .fvar x => if x = n then (.bvar m) else t1
  | .abs t1 => .abs (close t1 n (m + 1))
  | .app t11 t12 =>
    .app (close t11 n m) (close t12 n m)
  | .loc x => .loc x
  | .ref t1 => .ref (close t1 n m)
  | .deref t1 => .deref (close t1 n m)
  | .assign t1 t2 => .assign (close t1 n m) (close t2 n m)

@[simp]
def substF (Δ: venv) (t: tm) : tm :=
  match t with
  | .bool b => .bool b
  | .bvar _ => t
  | .fvar x =>
    match indexr x Δ with
    | none => t
    | some t' => t'
  | .abs t1 => .abs (substF Δ t1)
  | .app t11 t12 => .app (substF Δ t11) (substF Δ t12)
  | .loc x => .loc x
  | .ref t1 => .ref (substF Δ t1)
  | .deref t1 => .deref (substF Δ t1)
  | .assign t1 t2 => .assign (substF Δ t1) (substF Δ t2)

@[simp]
def closedF (t: tm) (n: ℕ) : Prop :=
  match t with
  | .bool _ => true
  | .bvar _ => true
  | .fvar x => x < n
  | .abs t1 => closedF t1 n
  | .app t11 t12 => closedF t11 n ∧ closedF t12 n
  | .loc _ => true
  | .ref t1 => closedF t1 n
  | .deref t1 => closedF t1 n
  | .assign t1 t2 => closedF t1 n ∧ closedF t2 n

@[simp]
def closedB (t: tm) (n: ℕ) : Prop :=
  match t with
  | .bool _ => true
  | .bvar x => x < n
  | .fvar _ => true
  | .abs t1 => closedB t1 (n + 1)
  | .app t11 t12 => closedB t11 n ∧ closedB t12 n
  | .loc _ => true
  | .ref t1 => closedB t1 n
  | .deref t1 => closedB t1 n
  | .assign t1 t2 => closedB t1 n ∧ closedB t2 n

@[simp]
def closedL (t: tm) (n: ℕ) : Prop :=
  match t with
  | .bool _ => true
  | .bvar _ => true
  | .fvar _ => true
  | .abs t1 => closedL t1 n
  | .app t11 t12 => closedL t11 n ∧ closedL t12 n
  | .loc x => x < n
  | .ref t1 => closedL t1 n
  | .deref t1 => closedL t1 n
  | .assign t1 t2 => closedL t1 n ∧ closedL t2 n

lemma openClosed : ∀ t n m,
  closedB (openSubst t m (.fvar n)) m →
  closedB t (m+1) := by
  intros t; induction t <;> intros n m h <;> simp
  case bvar x =>
    by_cases hx: (x = m)
    . omega
    . by_cases hx': (x < m)
      omega; unfold openSubst at h
      rw [if_neg hx] at h; have hx'' : (m < x) := by omega
      simp at h; omega
  case abs t ih =>
    apply ih n (m+1); unfold openSubst at h; simp at h; assumption
  case app t1 t2 ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2
  case ref t ih =>
    apply ih n m h
  case deref t ih =>
    apply ih n m h
  case assign t1 t2 ih1 ih2 =>
    simp at h; apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2

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
  case ref t ih =>
    apply ih n m h
  case deref t ih =>
    apply ih n m h
  case assign t1 t2 ih1 ih2 =>
    simp at h; apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2

lemma closedBOpenId: ∀ t1 t2 n,
  closedB t1 n -> openSubst t1 n t2 = t1 := by
  intros t1; induction t1 <;> intros t2 n h <;> simp
  case bvar x => intros hxn; simp at h; omega
  case abs t ih => simp at h; apply ih; assumption
  case app t1 t2 ih1 ih2 =>
    apply And.intro
    . apply ih1; apply h.1
    . apply ih2; apply h.2
  case ref t ih => apply ih; apply h
  case deref t ih => apply ih; apply h
  case assign t1 t2 ih1 ih2 =>
    simp at h; apply And.intro
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
  case ref t ih => apply ih; apply hcl; omega
  case deref t ih => apply ih; apply hcl; omega
  case assign t1 t2 ih1 ih2 =>
    simp at hcl; apply And.intro
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
  case ref t ih => apply ih; apply hcl
  case deref t ih => apply ih; apply hcl
  case assign t1 t2 ih1 ih2 =>
    simp at hcl; apply And.intro
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
  case ref t ih =>
    simp at h; apply ih; apply h; assumption
  case deref t ih =>
    simp at h; apply ih; apply h; assumption
  case assign t1 t2 ih1 ih2 =>
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
  case ref t ih => apply ih; apply hidx; assumption
  case deref t ih => apply ih; apply hidx; assumption
  case assign t1 t2 ih1 ih2 =>
    rcases hcl with ⟨hcl1, hcl2⟩
    apply And.intro
    . apply ih1; apply hidx; assumption
    . apply ih2; apply hidx; assumption

@[simp]
def binds x τ (Γ : tenv) := (indexr x Γ = some τ)

abbrev stty := List ty -- Φ, restricted to List .bool

inductive hasType : stty → tenv → tm → ty → Prop
| bool : ∀ Φ Γ b, hasType Φ Γ (.bool b) .bool
| var : ∀ Φ Γ x τ, binds x τ Γ → hasType Φ Γ (.fvar x) τ
| abs : ∀ Φ Γ t τ₁ τ₂,
  hasType Φ (τ₁::Γ) (openSubst t 0 (.fvar Γ.length)) τ₂ →
  closedF t Γ.length →
  hasType Φ Γ (.abs t) (ty.arrow τ₁ τ₂)
| app : ∀ Φ Γ t₁ t₂ τ₁ τ₂,
  hasType Φ Γ t₁ (.arrow τ₁ τ₂) →
  hasType Φ Γ t₂ τ₁ →
  hasType Φ Γ (.app t₁ t₂) τ₂
--| loc : ∀ Φ Γ n,
--  n < Φ.length →
--  hasType Φ Γ (.loc n) (.ref .bool)
| ref : ∀ Φ Γ t,
  hasType Φ Γ t (.bool) →
  hasType Φ Γ (.ref t) (.ref .bool)
| deref : ∀ Φ Γ t τ,
  hasType Φ Γ t (.ref .bool) →
  hasType Φ Γ (.deref t) .bool
| assign : ∀ Φ Γ t₁ t₂ τ,
  hasType Φ Γ t₁ (.ref .bool) →
  hasType Φ Γ t₂ .bool →
  hasType Φ Γ (.assign t₁ t₂) .bool -- for simplicity, we use bool for the result, could be unit

inductive value : tm → Prop
| bool : ∀ b, value (.bool b)
| loc : ∀ n, value (.loc n)
| abs : ∀ t, value (.abs t)

abbrev st := List tm

inductive step : st → tm → st → tm → Prop
| beta : ∀ σ t v,
  value v →
  step σ (.app (.abs t) v) σ (openSubst t 0 v)
| app1 : ∀ σ σ' t1 t1' t2,
  step σ t1 σ' t1' →
  step σ (.app t1 t2) σ' (.app t1' t2)
| app2 : ∀ σ σ' t1 t2 t2',
  value t1 →
  step σ t2 σ' t2' →
  step σ (.app t1 t2) σ' (.app t1 t2')
| ref_val : ∀ σ v,
  value v →
  step σ (.ref v) (v::σ) (.loc (σ.length))
| ref : ∀ σ σ' t t',
  step σ t σ' t' →
  step σ (.ref t) σ' (.ref t')
| deref_val : ∀ σ n v,
  indexr n σ = some v →
  step σ (.deref (.loc n)) σ v
| deref : ∀ σ σ' t t',
  step σ t σ' t' →
  step σ (.deref t) σ' (.deref t')
| assign_val : ∀ σ n v,
  -- n < σ.length →
  value v →
  step σ (.assign (.loc n) v) (update σ n v) v
| assign1 : ∀ σ σ' t1 t1' t2,
  step σ t1 σ' t1' →
  step σ (.assign t1 t2) σ' (.assign t1' t2)
| assign2 : ∀ σ σ' t1 t2 t2',
  value t1 →
  step σ t2 σ' t2' →
  step σ (.assign t1 t2) σ' (.assign t1 t2')

inductive stepn : st → tm → st → tm → Prop
| refl : ∀ σ t, stepn σ t σ t
| multi : ∀ σ1 σ2 σ3 t1 t2 t3, stepn σ1 t1 σ2 t2 → step σ2 t2 σ3 t3 → stepn σ1 t1 σ3 t3

lemma stepnTrans : ∀ σ1 σ2 σ3 t1 t2 t3, stepn σ1 t1 σ2 t2 → stepn σ2 t2 σ3 t3 → stepn σ1 t1 σ3 t3 := by
  intros σ1 σ2 σ3 t1 t2 t3 h1 h2; induction h2
  . assumption
  . case _ _ _ _ _ _ hstn hst ih =>
    apply stepn.multi; apply ih; assumption; assumption

lemma stepnApp1 : ∀ σ1 σ2 t1 t1' t2,
  stepn σ1 t1 σ2 t1' → stepn σ1 (.app t1 t2) σ2 (.app t1' t2) := by
  intros σ1 σ2 t1 t1' t2 h; induction h
  . constructor
  . case _ hstn hst ih => constructor; assumption; apply step.app1; assumption

lemma stepnApp2 : ∀ σ1 σ2 t1 t2 t2',
  value t1 → stepn σ1 t2 σ2 t2' → stepn σ1 (.app t1 t2) σ2 (.app t1 t2') := by
  intros σ1 σ2 t1 t2 t2' hv h; induction h
  . constructor
  . case _ hstn hst ih => apply stepn.multi; assumption; apply step.app2; assumption; assumption

lemma stepnBetaVal : ∀ σ1 t v,
  value v → stepn σ1 (.app (.abs t) v) σ1 (openSubst t 0 v) := by
  intros σ1 t v hv; apply stepn.multi; apply stepn.refl
  apply step.beta; assumption

lemma stepnBeta : ∀ σ1 σ2 σ3 σ4 f1 f2 t1 t2 t3,
  stepn σ1 f1 σ2 (.abs f2) →
  stepn σ2 t1 σ3 t2 →
  value t2 →
  stepn σ3 (openSubst f2 0 t2) σ4 t3 →
  stepn σ1 (.app f1 t1) σ4 t3 := by
  intros σ1 σ2 σ3 σ4 f1 f2 t1 t2 t3 h1 h2 hv h3
  have hstn1: stepn σ1 (.app f1 t1) σ2 (.app (.abs f2) t1) := by apply stepnApp1; assumption
  have hstn2: stepn σ2 (.app (.abs f2) t1) σ3 (.app (.abs f2) t2) := by apply stepnApp2; constructor; assumption
  have hstn3: stepn σ3 (.app (.abs f2) t2) σ3 (openSubst f2 0 t2) := by apply stepnBetaVal; assumption
  have hstn5: stepn σ1 (.app f1 t1) σ4 t3 := by
    apply stepnTrans; apply hstn1;
    apply stepnTrans; apply hstn2;
    apply stepnTrans; apply hstn3; assumption
  assumption

lemma stepnRef : ∀ σ1 σ2 t1 t2,
  stepn σ1 t1 σ2 t2 → stepn σ1 (.ref t1) σ2 (.ref t2) := by
  intros σ1 σ2 t1 t2 h; induction h
  . constructor
  . case _ hstn hst ih => constructor; assumption; apply step.ref; assumption

lemma stepnRefVal : ∀ σ1 v,
  value v → stepn σ1 (.ref v) (v::σ1) (.loc (σ1.length)) := by
  intros σ1 v hv; apply stepn.multi; apply stepn.refl;
  apply step.ref_val; assumption

lemma stepnDeref : ∀ σ1 σ2 t1 t2,
  stepn σ1 t1 σ2 t2 → stepn σ1 (.deref t1) σ2 (.deref t2) := by
  intros σ1 σ2 t1 t2 h; induction h
  . constructor
  . case _ hstn hst ih => constructor; assumption; apply step.deref; assumption

lemma stepnDerefVal : ∀ σ l v,
  indexr l σ = some v → stepn σ (.deref (.loc l)) σ v := by
  intros σ l v h; apply stepn.multi; apply stepn.refl;
  apply step.deref_val; assumption

lemma stepnAssign1 : ∀ σ1 σ2 t1 t1' t2,
  stepn σ1 t1 σ2 t1' → stepn σ1 (.assign t1 t2) σ2 (.assign t1' t2) := by
  intros σ1 σ2 t1 t1' t2 h; induction h
  . constructor
  . case _ hstn hst ih => constructor; assumption; apply step.assign1; assumption

lemma stepnAssign2: ∀ σ1 σ2 t1 t2 t2',
  value t1 → stepn σ1 t2 σ2 t2' → stepn σ1 (.assign t1 t2) σ2 (.assign t1 t2') := by
  intros σ1 σ2 t1 t2 t2' hv h; induction h
  . constructor
  . case _ hstn hst ih => apply stepn.multi; assumption; apply step.assign2; assumption; assumption

lemma stepnAssignVal : ∀ σ1 n v,
  value v → stepn σ1 (.assign (.loc n) v) (update σ1 n v) v := by
  intros σ1 n v hv; apply stepn.multi; apply stepn.refl;
  apply step.assign_val; assumption

lemma stepnAssign : ∀ σ1 σ2 σ3 t1 t2 l v,
  stepn σ1 t1 σ2 (tm.loc l) →
  stepn σ2 t2 σ3 v →
  value v →
  stepn σ1 (.assign t1 t2) (update σ3 l v) v := by
  intros σ1 σ2 σ3 t1 t2 l v h1 h2 hv;
  have hstn1: stepn σ1 (.assign t1 t2) σ2 (.assign (.loc l) t2) := by apply stepnAssign1; assumption
  have hstn2: stepn σ2 (.assign (.loc l) t2) σ3 (.assign (.loc l) v) := by apply stepnAssign2; constructor; assumption
  have hstn3: stepn σ1 (.assign t1 t2) σ3 (.assign (.loc l) v) := by apply stepnTrans <;> assumption
  have hstn4: stepn σ3 (.assign (.loc l) v) (update σ3 l v) v := by apply stepnAssignVal; assumption
  apply stepnTrans; apply hstn3; apply hstn4

-- the "world"
@[simp]
def st_rel := ℕ → ℕ → Prop

@[simp]
def st_rel.mt : st_rel := fun _ _ => false

@[simp]
def st_rel.ext (m: st_rel) (a b: ℕ): st_rel :=
  fun x y => (x = a ∧ y = b) ∨ (¬ x = a ∧ ¬ y = b ∧ m x y)

-- extend the "world"
@[simp]
def extend (m1 m2 : st_rel) : Prop := ∀ a b, m1 a b → m2 a b

notation:60 a:65 "≥" b:65 => extend a b

@[simp]
def bijection {X Y} (f: X → Y → Prop): Prop :=
  (∀ x y y', f x y → f x y' → y = y') ∧ (∀ x x' y, f x y → f x' y → x = x')

@[simp]
def storeType (σ1 σ2 : st) (m : st_rel) : Prop :=
  (∀ l1 l2, m l1 l2 → ∃ v, indexr l1 σ1 = some (.bool v) ∧ indexr l2 σ2 = some (.bool v)) ∧ bijection m

@[simp]
def valType (m: st_rel) (t1 : tm) (t2 : tm) (τ : ty) : Prop :=
  match t1, t2, τ with
  | .bool b1, .bool b2, .bool => b1 = b2
  | .loc n1, .loc n2, .ref τ => m n1 n2
  | (.abs t1), (.abs t2), .arrow τ1 τ2 =>
    ∀ v1 v2 m1 st1 st2,
    m ≥ m1 →
    storeType st1 st2 m1 →
    valType m1 v1 v2 τ1 → closedB v1 0 → closedB v2 0 →
    ∃ v3 v4 m2 st1' st2',
    m1 ≥ m2 ∧
    storeType st1' st2' m2 ∧
    stepn st1 (openSubst t1 0 v1) st1' v3 ∧ closedB v3 0 ∧
    stepn st2 (openSubst t2 0 v2) st2' v4 ∧ closedB v4 0 ∧
    valType m2 v3 v4 τ2
  | _, _, _ => false

@[simp]
def expType (st1 st2 : st) (m : st_rel) (t1 t2 : tm) (τ : ty) : Prop :=
  ∃ st1' st2' m' v1 v2,
    m ≥ m' ∧
    storeType st1' st2' m' ∧
    stepn st1 t1 st1' v1 ∧
    stepn st2 t2 st2' v2 ∧
    closedB v1 0 ∧ closedB v2 0 ∧
    valType m' v1 v2 τ

@[simp]
def envType (m : st_rel) (Δ1 : venv) (Δ2 : venv) (Γ : tenv) : Prop :=
  Δ1.length = Γ.length ∧
  Δ2.length = Γ.length ∧
  ∀ τ x, binds x τ Γ →
  ∃ v1 v2,
  indexr x Δ1 = some v1 ∧ closedB v1 0 ∧
  indexr x Δ2 = some v2 ∧ closedB v2 0 ∧
  valType m v1 v2 τ

@[simp]
def wf (t: tm) (Γ: tenv) := closedB t 0 ∧ closedF t (Γ.length)

@[simp]
def semType (Γ : tenv) (t1 t2 : tm) (τ : ty) : Prop :=
  ∀ st1 st2 m Δ1 Δ2,
  wf t1 Γ → wf t2 Γ →
  envType m Δ1 Δ2 Γ →
  storeType st1 st2 m →
  expType st1 st2 m (substF Δ1 t1) (substF Δ2 t2) τ

lemma valTypeValue : ∀ m t1 t2 τ, valType m t1 t2 τ → value t1 ∧ value t2 := by
  intros m t1 t2 τ h; cases t1 <;> cases t2 <;> try simp at h
  repeat apply And.intro <;> constructor

lemma extend.refl : ∀ m, m ≥ m := by intros m a b h; assumption

lemma extend.ext : ∀ st1 st2 m,
  storeType st1 st2 m →
  m ≥ (st_rel.ext m st1.length st2.length) :=
  by
  intros st1 st2 m h; simp;
  intros a b h'; right; rcases h with ⟨h1, h2⟩;
  specialize h1 _ _ h'; rcases h1 with ⟨v, hidx1, hidx2⟩;
  apply And.intro; apply indexrSome'' _ _ ⟨.bool v, hidx1⟩
  apply And.intro; apply indexrSome'' _ _ ⟨.bool v, hidx2⟩
  assumption

lemma extend.trans : ∀ {m1 m2 m3},
  m1 ≥ m2 → m2 ≥ m3 → m1 ≥ m3 := by
  intros m1 m2 m3 h12 h23 a b h; apply h23; apply h12; assumption

lemma envType.empty : envType st_rel.mt [] [] [] := by simp

lemma envType.extend : ∀ m Δ1 Δ2 Γ v1 v2 τ,
  envType m Δ1 Δ2 Γ →
  closedB v1 0 → closedB v2 0 →
  valType m v1 v2 τ →
  envType m (v1::Δ1) (v2::Δ2) (τ::Γ) := by
  intros m Δ1 Δ2 Γ v1 v2 τ henv hclv1 hclv2 hv12
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

lemma envType.closed : ∀ m Δ1 Δ2 Γ, envType m Δ1 Δ2 Γ →
  (∀ x t1, indexr x Δ1 = some t1 → closedB t1 0) ∧
  (∀ x t1, indexr x Δ2 = some t1 → closedB t1 0) := by
  intros m Δ1 Δ2 Γ henv; rcases henv with ⟨hlen1, hlen2, h⟩
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

lemma storeType.mt : storeType [] [] st_rel.mt := by
  constructor; intros l1 l2 h; cases h; simp

lemma storeType.ext : ∀ σ1 σ2 m v1 v2,
  storeType σ1 σ2 m →
  valType m v1 v2 .bool →
  storeType (v1::σ1) (v2::σ2) (st_rel.ext m σ1.length σ2.length) := by
  intros σ1 σ2 m v1 v2 hst hv12
  rcases hst with ⟨h1, h2⟩
  apply And.intro
  . intros l1 l2 m'; cases m' with
    | inl h =>
      rw [h.1, h.2]; rw [indexrHead]; rw [indexrHead]
      cases v1 <;> cases v2 <;> simp at hv12
      rename_i v1 v2; rw [hv12]; exists v2
    | inr h =>
      specialize h1 l1 l2 h.2.2
      rcases h1 with ⟨v, hidx1, hidx2⟩
      exists v; rw [indexrSkip, indexrSkip]; aesop; aesop; aesop
  . rcases h2 with ⟨h21, h22⟩; aesop

lemma storeType.update : ∀ st1 st2 m v1 v2 l1 l2,
  storeType st1 st2 m →
  valType m v1 v2 .bool →
  m l1 l2 →
  storeType (update st1 l1 v1) (update st2 l2 v2) m := by
  intros st1 st2 m v1 v2 l1 l2 hst hv12 hm
  rcases hst with ⟨h1, h2, h3⟩
  apply And.intro
  . intros l1' l2' hm'
    by_cases h': l1 = l1' <;> by_cases h'': l2 = l2'
    . subst h'; subst h''
      specialize h1 l1 l2 hm; rcases h1 with ⟨v, hidx1, hidx2⟩
      rw [indexrUpdateHit]; rw [indexrUpdateHit]
      cases v1 <;> cases v2 <;> simp at hv12;
      rename_i v1 v2; rw [hv12]; exists v2
      apply indexrSome'; grind; apply indexrSome'; grind
    . subst h'; have c : l2 = l2' := by apply h2; apply hm; apply hm'
      contradiction
    . subst h''; have c : l1 = l1' := by apply h3; apply hm; apply hm'
      contradiction
    . specialize h1 l1' l2' hm'; rcases h1 with ⟨v, hidx1, hidx2⟩
      exists v; rw [indexrUpdateMiss]; rw [indexrUpdateMiss];
      apply And.intro <;> assumption; omega; omega
  . aesop

lemma valType.antimono : ∀ m1 m2 v1 v2 τ,
  valType m1 v1 v2 τ → m1 ≥ m2 → valType m2 v1 v2 τ := by
  intros m1 m2 v1 v2 τ hv12 hm;
  cases v1 <;> cases v2 <;> try simp at hv12
  . rename_i v1 v2;
    cases v1 <;> cases v2 <;> cases τ <;> try simp at hv12 <;> simp
  . cases τ; simp at hv12; simp at hv12
    next t1 t2 τ1 τ2 =>
    intros v3 v4 m3 st1 st2 hm'
    specialize hv12 v3 v4 m3 st1 st2 (extend.trans hm hm'); assumption
  . cases τ <;> try simp at hv12 <;> aesop

lemma envType.antimono : ∀ m1 m2 Δ1 Δ2 Γ,
  envType m1 Δ1 Δ2 Γ → m1 ≥ m2 → envType m2 Δ1 Δ2 Γ := by
  intros m1 m2 Δ1 Δ2 Γ henv hm; rcases henv with ⟨hlen1, hlen2, h⟩
  constructor; aesop; constructor; aesop
  intros τ x hbd; rcases h τ x hbd with ⟨v1, v2, hidxv1, hclv1, hidxv2, hclv2, hv12⟩
  specialize h τ x hbd; aesop; apply valType.antimono; apply hv12; apply hm

-- compatibility lemmas

lemma semBool : ∀ Γ b, semType Γ (.bool b) (.bool b) .bool := by
  intros Γ b st1 st2 m Δ1 Δ2 _ _ _ _;
  exists st1, st2, m, (.bool b), (.bool b);
  apply And.intro; apply extend.refl; apply And.intro; assumption;
  simp; apply And.intro <;> apply stepn.refl

lemma semVar : ∀ Γ x τ, binds x τ Γ → semType Γ (.fvar x) (.fvar x) τ := by
  intros Γ x τ hbd st1 st2 m Δ1 Δ2 _ _ henv hst
  rcases henv with ⟨_, _, h⟩
  have ⟨v1, v2, idx1, cl1, idx2, cl2, semv⟩ := h τ x hbd
  exists st1, st2, m, v1, v2; simp [idx1, idx2]
  apply And.intro; simp at hst; exact hst
  exact ⟨stepn.refl st1 v1, stepn.refl st2 v2, cl1, cl2, semv⟩

lemma semRef : ∀ Γ t1 t2,
  semType Γ t1 t2 .bool →
  semType Γ (.ref t1) (.ref t2) (.ref .bool) := by
  intros Γ t1 t2 hsem st1 st2 m Δ1 Δ2 wf1 wf2 henv hst
  have hexp := hsem st1 st2 m Δ1 Δ2 wf1 wf2 henv hst
  rcases hexp with ⟨st1', st2', m', v1, v2, hm1, hstore, hstep1, hstep2, hcl1, hcl2, hv12⟩
  have hm3 := extend.trans hm1 (extend.ext st1' st2' m' hstore)
  exists (v1::st1'), (v2::st2'), (st_rel.ext m' st1'.length st2'.length), (.loc st1'.length), (.loc st2'.length)
  constructor; apply hm3
  constructor; apply storeType.ext; assumption; assumption
  simp; constructor; apply stepnTrans; apply stepnRef; apply hstep1
  apply stepnRefVal; exact (valTypeValue _ _ _ _ hv12).1
  apply stepnTrans; apply stepnRef; apply hstep2
  apply stepnRefVal; exact (valTypeValue _ _ _ _ hv12).2

lemma semDeref : ∀ Γ t1 t2,
  semType Γ t1 t2 (.ref .bool) →
  semType Γ (.deref t1) (.deref t2) .bool := by
  intros Γ t1 t2 hsem st1 st2 m Δ1 Δ2 wf1 wf2 henv hst
  have hexp := hsem st1 st2 m Δ1 Δ2 wf1 wf2 henv hst
  rcases hexp with ⟨st1', st2', m', v1, v2, hm1, hstore, hstep1, hstep2, hv12⟩
  cases v1 <;> cases v2 <;> simp at hv12
  rename_i l1 l2; rcases hstore.1 l1 l2 hv12 with ⟨b, hidx1, hidx2⟩
  exists st1', st2', m', .bool b, .bool b;
  apply And.intro; assumption; apply And.intro; assumption; simp
  apply And.intro
  . have hstn1 : stepn st1 (.deref (substF Δ1 t1)) st1' (.deref (.loc l1)) := by
      apply stepnDeref; assumption
    have hstn2 : stepn st1' (.deref (.loc l1)) st1' (.bool b) := by
      apply stepnDerefVal; assumption
    apply stepnTrans; apply hstn1; apply hstn2
  . have hstn1 : stepn st2 (.deref (substF Δ2 t2)) st2' (.deref (.loc l2)) := by
      apply stepnDeref; assumption
    have hstn2 : stepn st2' (.deref (.loc l2)) st2' (.bool b) := by
      apply stepnDerefVal; assumption
    apply stepnTrans; apply hstn1; apply hstn2

lemma wfAssign : ∀ {t1 t2 Γ},
  wf (.assign t1 t2) Γ →  wf t1 Γ ∧ wf t2 Γ := by
  intros t1 t2 Γ h; simp at h; constructor; aesop; aesop

lemma wfApp : ∀ {f t Γ},
  wf (.app f t) Γ →  wf f Γ ∧ wf t Γ := by
  intros f t Γ h; simp at h; constructor; aesop; aesop

lemma semAssign : ∀ Γ t1 t2 t1' t2',
  semType Γ t1 t1' (.ref .bool) →
  semType Γ t2 t2' .bool →
  semType Γ (.assign t1 t2) (.assign t1' t2') .bool := by
  intros Γ t1 t2 t1' t2' hsem1 hsem2 st1 st2 m Δ1 Δ2 wf1 wf2 henv hst
  have hexp1 := hsem1 st1 st2 m Δ1 Δ2 (wfAssign wf1).1 (wfAssign wf2).1 henv hst
  rcases hexp1 with ⟨st1', st2', m', v1, v2, hm1, hstore, hstep1, hstep2, hclv1, hclv2, hv12⟩
  have henv' : envType m' Δ1 Δ2 Γ := by apply envType.antimono; apply henv; apply hm1
  have hexp2 := hsem2 st1' st2' m' Δ1 Δ2 (wfAssign wf1).2 (wfAssign wf2).2 henv' hstore
  rcases hexp2 with ⟨st1'', st2'', m'', v1', v2', hm2, hstore2, hstep1', hstep2', hclv1', hclv2', hv12'⟩
  cases v1 <;> cases v2 <;> simp at hv12
  rename_i l1 l2; rcases hstore.1 l1 l2 hv12 with ⟨b, hidx1, hidx2⟩
  exists (update st1'' l1 v1'), (update st2'' l2 v2'), m'', v1', v2'
  constructor; apply extend.trans; apply hm1; apply hm2
  constructor; apply storeType.update; assumption; assumption; apply hm2; assumption
  apply And.intro
  . simp; have hv := (valTypeValue _ _ _ _ hv12').1
    apply stepnAssign <;> assumption
  . constructor; have hv := (valTypeValue _ _ _ _ hv12').2
    apply stepnAssign <;> assumption; grind

lemma semApp : ∀ Γ f1 f2 t1 t2 τ1 τ2,
  semType Γ f1 f2 (.arrow τ1 τ2) →
  semType Γ t1 t2 τ1 →
  semType Γ (.app f1 t1) (.app f2 t2) τ2 := by
  intros Γ f1 f2 t1 t2 τ1 τ2 hsemf hsemt st1 st2 m Δ1 Δ2 wf1 wf2 henv hst
  have hexpf := hsemf st1 st2 m Δ1 Δ2 (wfApp wf1).1 (wfApp wf2).1 henv hst
  rcases hexpf with ⟨st1', st2', m1, f1', f2', hm1, hstore, hstepf1, hstepf2, hclf1, hclf2, hf12⟩
  have henv' : envType m1 Δ1 Δ2 Γ := by apply envType.antimono; apply henv; apply hm1
  have hexpt := hsemt st1' st2' m1 Δ1 Δ2 (wfApp wf1).2 (wfApp wf2).2 henv' hstore
  rcases hexpt with ⟨st1'', st2'', m2, t1', t2', hm2, hstore2, hstept1, hstept2, hclt1, hclt2, ht12⟩
  cases f1' <;> cases f2' <;> try contradiction
  rename_i t3 t4
  specialize hf12 t1' t2' m2 st1'' st2'' hm2 hstore2 ht12 hclt1 hclt2
  have ⟨v5, v6, m3, st3, st4, hm3, hstore3, hstbt1, hstbt2, hclv5, hclv6, hv56⟩ := hf12
  exists st3, st4, m3, v5, v6
  constructor; apply extend.trans; apply hm1; apply extend.trans; apply hm2; apply hm3
  constructor; assumption; constructor; simp
  apply stepnBeta; assumption; assumption; exact (valTypeValue _ _ _ _ ht12).1
  assumption; constructor; simp
  apply stepnBeta; assumption; assumption; exact (valTypeValue _ _ _ _ ht12).2
  assumption; constructor; assumption; constructor; assumption; assumption

lemma lenInc: ∀ {A} x (L : List A), L.length + 1 = (x::L).length := by intros _ L x; simp

lemma envTypeClosed : ∀ m Δ1 Δ2 Γ, envType m Δ1 Δ2 Γ →
  (∀ x t1, indexr x Δ1 = some t1 → closedB t1 0) ∧
  (∀ x t1, indexr x Δ2 = some t1 → closedB t1 0) := by
  intros m Δ1 Δ2 Γ henv; rcases henv with ⟨hlen1, hlen2, h⟩
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

lemma envTypeExtend : ∀ m Δ1 Δ2 Γ v1 v2 τ,
  envType m Δ1 Δ2 Γ →
  closedB v1 0 → closedB v2 0 →
  valType m v1 v2 τ →
  envType m (v1::Δ1) (v2::Δ2) (τ::Γ) := by
  intros m Δ1 Δ2 Γ v1 v2 τ henv hclv1 hclv2 hv12
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

lemma semAbs : ∀ Γ t1 t2 τ1 τ2,
  semType (τ1::Γ) (openSubst t1 0 (.fvar Γ.length)) (openSubst t2 0 (.fvar Γ.length)) τ2 →
  semType Γ (.abs t1) (.abs t2) (.arrow τ1 τ2) := by
  intros Γ t1 t2 τ1 τ2 hsem st1 st2 m Δ1 Δ2 wf1 wf2 henv hst
  exists st1, st2, m, (substF Δ1 (.abs t1)), (substF Δ2 (.abs t2))
  constructor; apply extend.refl; constructor; assumption
  constructor; apply stepn.refl
  constructor; apply stepn.refl
  simp at wf1; simp at wf2
  have hclb1' := openClosed' t1 (Γ.length) 0 wf1.1
  have hclb2' := openClosed' t2 (Γ.length) 0 wf2.1
  have envcl := envTypeClosed m Δ1 Δ2 Γ henv
  constructor; apply substFClosedBComm _ _ _ envcl.1 wf1.1
  constructor; apply substFClosedBComm _ _ _ envcl.2 wf2.1
  intros v1 v2 m' st1' st2' hm hst hval12 hclv1 hclv2
  have henv1 := envType.antimono m m' Δ1 Δ2 Γ henv hm
  have henv2 := envTypeExtend m' Δ1 Δ2 Γ v1 v2 τ1 henv1 hclv1 hclv2 hval12
  have clf1' := closedFInc _ _ 0 wf1.2
  have clf2' := closedFInc _ _ 0 wf2.2
  have hsem' := hsem st1' st2' m' (v1::Δ1) (v2::Δ2) ⟨hclb1', clf1'⟩ ⟨hclb2', clf2'⟩ henv2 hst
  rcases hsem' with ⟨st1'', st2'', m'', vr1, vr2, hm', hst'', hst1, hst2, hclvr1, hclvr2, semvr⟩
  rw [<-henv.1] at hst1; rw [<-henv.2.1] at hst2
  rw [substFOpenComm] at hst1; rw [substFOpenComm] at hst2
  exists vr1, vr2, m'', st1'', st2''
  rw [henv.2.1]; exact wf2.2;  exact envcl.2; rw [henv.1]; exact wf1.2; exact envcl.1

theorem fundamental : ∀ Φ Γ t τ,
  hasType Φ Γ t τ → semType Γ t t τ := by
  intros Φ Γ t τ h; induction h
  case bool => apply semBool
  case var => apply semVar; assumption
  case abs => apply semAbs; assumption
  case app => apply semApp <;> assumption
  case ref => apply semRef; assumption
  case deref => apply semDeref; assumption
  case assign => apply semAssign <;> assumption

lemma hasTypeClosedB : ∀ Φ Γ t τ, hasType Φ Γ t τ → closedB t 0 := by
  intros Φ Γ t τ h; induction h <;> simp
  case abs => apply openClosed; assumption
  case app => apply And.intro <;> assumption
  case ref => assumption
  case deref => assumption
  case assign => apply And.intro <;> assumption

lemma substFMt: ∀ t, substF [] t = t := by
  intros t; induction t <;> simp <;> try assumption
  apply And.intro <;> assumption
  apply And.intro <;> assumption

lemma hasTypeClosedF : ∀ Φ t τ, hasType Φ [] t τ → closedF t 0 := by
  intros Φ t τ h; revert τ; induction t <;> intros τ h <;> simp
  . case fvar x => cases h; next bd => simp at bd
  . case abs t ih => cases h; assumption
  . case app t1 t2 ih1 ih2 =>
    cases h; apply And.intro
    . apply ih1; assumption
    . apply ih2; assumption
  . case ref t ih => cases h; apply ih; assumption
  . case deref t ih => cases h; apply ih; assumption
  . case assign t1 t2 ih1 ih2 =>
    cases h; apply And.intro
    . apply ih1; assumption
    . apply ih2; assumption

lemma hasTypeWf : ∀ Φ t τ, hasType Φ [] t τ → wf t [] := by
  intros Φ t τ h; constructor
  . apply hasTypeClosedB; assumption
  . apply hasTypeClosedF; assumption

theorem safety : ∀ t τ, hasType [] [] t τ → expType [] [] st_rel.mt t t τ := by
  intros t τ h
  have hsem := fundamental [] [] t τ h
  have henv : envType st_rel.mt [] [] [] := by apply envType.empty
  have hst : storeType [] [] st_rel.mt := by apply storeType.mt
  have hexp := hsem [] [] st_rel.mt [] [] (hasTypeWf [] t τ h) (hasTypeWf [] t τ h) henv hst
  rcases hexp with ⟨st1, st2, m, v1, v2, hm, hstore, hst1, hst2, hclb1, hclb2, hval⟩
  exists st1, st2, m, v1, v2
  constructor; assumption
  constructor; assumption
  constructor; rw [substFMt] at hst1; assumption
  constructor; rw [substFMt] at hst2; assumption
  exact ⟨hclb1, hclb2, hval⟩
