-- STLC + locally nameless with cofinite quantification

-- Roughly following the following materials:
-- https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc/STLC_Tutorial.html
-- https://github.com/ElifUskuplu/Stlc_deBruijn

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort

inductive ty : Type
| unit : ty
| arrow : ty → ty → ty

inductive tm : Type
| bvar : ℕ → tm
| fvar : ℕ → tm
| abs : tm → tm
| app : tm → tm → tm

-- free variable substitution
@[simp]
def substF (src : ℕ) (tgt : tm) : tm → tm
| .bvar i => .bvar i
| .fvar i => if i = src then tgt else .fvar i
| .abs t => .abs (substF src tgt t)
| .app t₁ t₂ => .app (substF src tgt t₁) (substF src tgt t₂)

example :
  substF 0 (.fvar 1) (.abs (.app (.bvar 0) (.fvar 0))) =
  .abs (.app (.bvar 0) (.fvar 1)) := by simp

@[simp]
def fv : (t: tm) -> Finset ℕ
| .bvar _ => {}
| .fvar i => {i}
| .abs t => fv t
| .app t₁ t₂ => fv t₁ ∪ fv t₂

example : fv (.abs (.app (.bvar 0) (.fvar 0))) = {0} := by simp

lemma substFresh (src : ℕ) (tgt : tm) (t: tm) (h : src ∉ fv t) :
  substF src tgt t = t := by
  induction t generalizing src tgt
  case bvar => simp
  case fvar i => simp; intro heq; rw [heq] at h; simp [fv] at h
  case abs t₁ ih => simp; apply ih; simp at h; assumption
  case app t₁ t₂ ih₁ ih₂ =>
    simp; simp at h
    apply And.intro (ih₁ src tgt h.left) (ih₂ src tgt h.right)

-- we assume `tgt` is locally closed, so we do not need
-- to shift indices in tgt.
-- we assume the function is initially called with `src = 0`
@[simp]
def openRec (src : ℕ) (tgt: tm) : tm → tm
| .bvar i => if src == i then tgt else (.bvar i)
| .fvar i => .fvar i
| .abs t => .abs (openRec (.succ src) tgt t)
| .app t₁ t₂ => .app (openRec src tgt t₁) (openRec src tgt t₂)

-- substitute `tgt` for index 0 in `t` (i.e. open)
@[simp]
def substB (t: tm) (tgt: tm) : tm := openRec 0 tgt t

example : substB (.bvar 0) (.fvar 0) = (.fvar 0) := by simp
example : substB
  (.app (.abs (.app (.bvar 1) (.bvar 0))) (.bvar 0)) (.fvar 0) =
  (.app (.abs (.app (.fvar 0) (.bvar 0))) (.fvar 0)) :=
  by simp

-- locally closed expression: no indices appearing in it are unbound

inductive lc : tm → Prop
| lc_var : ∀ x, lc (.fvar x)
| lc_abs : ∀ (L: Finset ℕ) (t : tm),
  -- cofinite quantification
  (∀ (x : ℕ), x ∉ L → lc (substB t (.fvar x))) → lc (.abs t)
| lc_app : ∀ t₁ t₂, lc t₁ → lc t₂ → lc (.app t₁ t₂)

example : lc (.abs (.bvar 0)) := by
  apply (lc.lc_abs {0} (.bvar 0))
  intro x h; constructor

example : lc (.abs (.fvar 0)) := by
  apply (lc.lc_abs {0} (.fvar 0))
  intro x h; simp; constructor

lemma openRecLc' : ∀ e j v i u,
  ¬ (i = j) →
  openRec j v e = openRec i u (openRec j v e) →
  e = openRec i u e :=
by
  intro e j v i u  hneq H
  induction e generalizing j v i u
  case bvar k =>
    by_cases hjk: (j = k)
    . rw [hjk] at H; simp at H; rw [hjk] at hneq; simp; rw [if_neg hneq]
    . simp; simp at H; rw [if_neg hjk] at H;
      by_cases hik: (i = k)
      . rw [hik]; simp; simp at H; rw [hik] at H; simp at H; assumption
      . rw [if_neg hik]
  case fvar k => simp
  case abs t ih => simp; simp at H; apply (@ih (j + 1)); simp; assumption; assumption
  case app t₁ t₂ ih₁ ih₂ =>
    simp; simp at H;
    obtain ⟨ha, hb⟩ := H
    apply And.intro
    . apply (@ih₁ j); assumption; assumption
    . apply (@ih₂ j); assumption; assumption

-- From https://github.com/ElifUskuplu/Stlc_deBruijn/blob/main/Stlc/basics.lean
-- We can always pick a fresh variable for a given term out of a fixed set.
lemma pick_fresh (t : tm) (L : Finset ℕ) : ∃ (x : ℕ), x ∉ (L ∪ fv t) := by
  exact Infinite.exists_not_mem_finset (L ∪ fv t)

lemma pick_fresh' (L : Finset ℕ) : ∃ (x : ℕ), x ∉ L := by
  exact Infinite.exists_not_mem_finset L

-- index substitution has no effect on locally closed term
lemma openRecLc0 : ∀ i u e, lc e → e = openRec i u e := by
  intro i u e h
  induction h generalizing i u <;> simp
  case lc_abs L t' lc' ih =>
    let ⟨x, hx⟩ := pick_fresh' L;
    apply openRecLc' (i := i+1) (j := 0); simp; apply ih; assumption
  case lc_app t₁ t₂ ih₁ ih₂ => apply And.intro (ih₁ i u) (ih₂ i u)

-- free var subst distributes over index subst (openRec)
lemma substOpenRec : ∀ t1 t2 u x k,
  lc u → substF x u (openRec k t2 t1) = openRec k (substF x u t2) (substF x u t1) :=
by
  intro t1 t2 u x k Hlc
  induction t1 generalizing k
  case bvar i =>
    simp; by_cases h: (i = k)
    . rw [h]; simp
    . have h' := Ne.symm h; rw [if_neg h']; rw [if_neg h']; simp
  case fvar i =>
    simp; by_cases h: (i = x)
    . rw [h]; simp; apply openRecLc0; assumption
    . rw [if_neg h]; simp
  case abs t ih => simp; apply ih
  case app t1 t2 ih₁ ih₂ => simp; apply And.intro (ih₁ k) (ih₂ k)

lemma substOpenVar : ∀ (x y : ℕ) u e, y ≠ x → lc u →
  substB (substF x u e) (.fvar y) = substF x u (substB e (.fvar y)) :=
by
  intro x y u e hneq hlc
  simp; rw [substOpenRec]; simp; rw [if_neg hneq]; assumption

lemma substLc : ∀ (x : ℕ) u e, lc e → lc u → lc (substF x u e) := by
  intro x u e h1 h2
  induction h1 generalizing x u
  case lc_var y =>
    simp; by_cases h: (y = x)
    . rw [h]; simp; assumption
    . rw [if_neg h]; constructor
  case lc_abs L t h ih =>
    simp; apply (lc.lc_abs (L ∪ {x}))
    intro y hy; simp at hy; push_neg at hy; rw [substOpenVar];
    apply ih; exact hy.left; assumption; exact hy.right; assumption
  case lc_app t1 t2 ht1 ht2 => simp; constructor; apply ht1; assumption; apply ht2; assumption

abbrev ctx := List (ℕ × ty)

-- @[simp] def dom (ρ : ctx) : Finset ℕ := ρ.map Prod.fst |>.toFinset
-- #eval dom [(0, .unit), (1, .arrow .unit .unit)]

@[simp]
def get (x : ℕ) : ctx → Option ty
| [] => none
| (y , S) :: Γ' => if x = y then some S else get x Γ'

@[simp]
def dom : ctx → (Finset ℕ)
| [] => ∅
| ((x, _) :: Γ') => {x} ∪ (dom Γ')

@[simp]
def binds x T (Γ : ctx) := (get x Γ = some T)

@[simp]
def inCtx (x : ℕ) : ctx → Prop
| [] => False
| (y, _) :: Γ' => x = y ∨ inCtx x Γ'

lemma memDomIffInCtx(a : ℕ) (Γ : ctx) : a ∈ dom Γ ↔ inCtx a Γ := by
  induction Γ
  case nil => simp [Finset.not_mem_empty]
  case cons b Γ' f => simp [Finset.mem_union, Finset.mem_singleton]; rw [f]

inductive ctxOk : ctx → Prop
| ctxOK_mt : ctxOk []
| ctxOK_cs : ∀ Γ x τ,
  ctxOk Γ → (¬ inCtx x Γ) → ctxOk ((x, τ) :: Γ)

lemma bindsInCtx (x : ℕ) (τ : ty) (Γ : ctx) :
  binds x τ Γ → inCtx x Γ := by
  intro h; induction Γ <;> simp at h
  case cons hd tl ih =>
  by_cases heq: (x = hd.1)
  . simp [heq];
  . simp [heq]; apply ih; rw [if_neg heq] at h; assumption

lemma inCtxBinds (x : ℕ) (Γ : ctx) :
  inCtx x Γ → exists (τ : ty), binds x τ Γ := by
  intro h; induction Γ <;> simp at h
  case cons hd tl ih =>
    by_cases heq: (x = hd.1)
    . simp [heq];
    . simp [heq]; apply Or.elim h <;> intro h
      . contradiction
      . apply ih h

lemma bindsConcatOk x τ (Γ₁ Γ₂ : ctx) :
  binds x τ Γ₁ -> ctxOk (Γ₂ ++ Γ₁) -> binds x τ (Γ₂ ++ Γ₁) := by
  induction Γ₂
  case nil => simp; intros; assumption
  case cons b Γ' ih =>
    intro hbd H; cases H
    next y τ' hctx g =>
      simp at hctx
      by_cases hxy : x = y
      . simp [if_pos hxy]
        by_contra; apply g
        apply bindsInCtx y τ (Γ' ++ Γ₁)
        rw [← hxy]; apply ih <;> assumption
      . simp [if_neg hxy]; apply ih <;> assumption

lemma weakeningBind Γ₁ Γ₂ Γ₃ x τ:
  binds x τ (Γ₁ ++ Γ₃) →
  ctxOk (Γ₁ ++ Γ₂ ++ Γ₃) →
  binds x τ (Γ₁ ++ Γ₂ ++ Γ₃) := by
  intro hb hctx
  induction Γ₁
  case nil => simp at *; apply bindsConcatOk; assumption; assumption
  case cons hd tl ih =>
    simp; by_cases heq: (x = hd.1) <;> simp at hb;
    . simp [heq]; simp [heq] at hb; assumption
    . simp [if_neg heq]; simp at ih; apply ih;
      simp [heq] at hb; assumption;
      cases hctx; next hctx' _ => simp at hctx'; assumption;

inductive hasType : ctx → tm → ty → Prop
| t_var : ∀ Γ x τ, ctxOk Γ → binds x τ Γ → hasType Γ (.fvar x) τ
| t_abs : ∀ (L : Finset ℕ) Γ t τ₁ τ₂,
  (∀ (x: ℕ), x ∉ L → hasType ((x, τ₁)::Γ) (substB t (.fvar x)) τ₂) →
  hasType Γ (.abs t) (ty.arrow τ₁ τ₂)
| t_app : ∀ Γ t₁ t₂ τ₁ τ₂,
  hasType Γ t₁ (.arrow τ₁ τ₂) →
  hasType Γ t₂ τ₁ →
  hasType Γ (.app t₁ t₂) τ₂

-- weakening of typing

lemma weakening'' : ∀ (Γ' Γ₂ Γ₃ : ctx) t τ,
  hasType Γ' t τ →
  (Γ₁ : ctx) → Γ' = Γ₁ ++ Γ₂ →
  ctxOk (Γ₁ ++ Γ₃ ++ Γ₂) →
  hasType (Γ₁ ++ Γ₃ ++ Γ₂) t τ := by
  intro Γ' Γ₂ Γ₃ t τ hty
  induction hty
  case t_var Γ' x' τ' hctx bd =>
    intros Γ₁ heq hctx'; constructor; assumption
    apply weakeningBind; rw [heq] at bd; assumption; assumption
  case t_abs L Γ t τ₁ τ₂ _ ih =>
    intros Γ₁ heq hctx';
    apply hasType.t_abs (L ∪ dom (Γ₁ ++ Γ₃ ++ Γ₂))
    intro x hx; simp at hx
    apply ih x hx.1 ((x, τ₁) :: Γ₁)
    simp; assumption
    simp; apply ctxOk.ctxOK_cs; rw [<- List.append_assoc]; assumption
    intro hctx; exact (hx.2 ((memDomIffInCtx _ _).mpr hctx))
  case t_app Γ t1 t2 τ1 τ2 ty1 ty2 ih1 ih2 =>
    intros Γ₁ heq hctx; apply hasType.t_app
    exact (ih1 Γ₁ heq hctx); exact (ih2 Γ₁ heq hctx)

lemma weakening' : ∀ (Γ₁ Γ₂ Γ₃ : ctx) t τ,
  hasType (Γ₁ ++ Γ₃) t τ →
  ctxOk (Γ₁ ++ Γ₂ ++ Γ₃) →
  hasType (Γ₁ ++ Γ₂ ++ Γ₃) t τ := by
  intros Γ₁ Γ₂ Γ₃ t τ hty hctx
  apply weakening''; assumption; rfl; assumption

lemma weakening : ∀ Γ₁ Γ₂ t τ,
  hasType Γ₂ t τ →
  ctxOk (Γ₁ ++ Γ₂) →
  hasType (Γ₁ ++ Γ₂) t τ := by
  intro Γ₁ Γ₂ t τ hty hctx
  rw [<- List.nil_append (Γ₁ ++ Γ₂)]
  apply weakening' [] Γ₁ Γ₂ t τ hty
  simp; assumption
