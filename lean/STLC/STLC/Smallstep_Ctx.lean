-- STLC
-- locally nameless with cofinite quantification
-- call-by-value, contextual reduction semantics

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort

namespace Smallstep_Ctx

inductive ty : Type
| unit : ty
| arrow : ty → ty → ty

inductive tm : Type
| bvar : ℕ → tm
| fvar : ℕ → tm
| abs : tm → tm
| app : tm → tm → tm

@[simp]
def substF (src : ℕ) (tgt : tm) : tm → tm
| .bvar i => .bvar i
| .fvar i => if i = src then tgt else .fvar i
| .abs t => .abs (substF src tgt t)
| .app t₁ t₂ => .app (substF src tgt t₁) (substF src tgt t₂)

@[simp]
def fv : (t: tm) -> Finset ℕ
| .bvar _ => {}
| .fvar i => {i}
| .abs t => fv t
| .app t₁ t₂ => fv t₁ ∪ fv t₂

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

inductive lc : tm → Prop
| lc_var : ∀ x, lc (.fvar x)
| lc_abs : ∀ (L: Finset ℕ) (t : tm),
  -- cofinite quantification
  (∀ (x : ℕ), x ∉ L → lc (substB t (.fvar x))) → lc (.abs t)
| lc_app : ∀ t₁ t₂, lc t₁ → lc t₂ → lc (.app t₁ t₂)

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

lemma substIntro (x : ℕ) u e:
  x ∉ (fv e) → lc u → substB e u = substF x u (substB e (.fvar x)) := by
  intro hx hlc; simp; rw [substOpenRec]; simp;
  rw [substFresh]; assumption; assumption

abbrev env := List (ℕ × ty)

@[simp]
def get (x : ℕ) : env → Option ty
| [] => none
| (y , S) :: Γ' => if x = y then some S else get x Γ'

@[simp]
def dom : env → (Finset ℕ)
| [] => ∅
| ((x, _) :: Γ') => {x} ∪ (dom Γ')

@[simp]
def binds x T (Γ : env) := (get x Γ = some T)

@[simp]
def inEnv(x : ℕ) : env → Prop
| [] => False
| (y, _) :: Γ' => x = y ∨ inEnv x Γ'

lemma memDomIffInEnv(a : ℕ) (Γ : env) : a ∈ dom Γ ↔ inEnv a Γ := by
  induction Γ
  case nil => simp [Finset.not_mem_empty]
  case cons b Γ' f => simp [Finset.mem_union, Finset.mem_singleton]; rw [f]

inductive envOk : env → Prop
| envOK_mt : envOk []
| envOK_cs : ∀ Γ x τ,
  envOk Γ → (¬ inEnv x Γ) → envOk ((x, τ) :: Γ)

lemma bindsInEnv (x : ℕ) (τ : ty) (Γ : env) :
  binds x τ Γ → inEnv x Γ := by
  intro h; induction Γ <;> simp at h
  case cons hd tl ih =>
  by_cases heq: (x = hd.1)
  . simp [heq];
  . simp [heq]; apply ih; rw [if_neg heq] at h; assumption

lemma inCtxBinds (x : ℕ) (Γ : env) :
  inEnv x Γ → exists (τ : ty), binds x τ Γ := by
  intro h; induction Γ <;> simp at h
  case cons hd tl ih =>
    by_cases heq: (x = hd.1)
    . simp [heq];
    . simp [heq]; apply Or.elim h <;> intro h
      . contradiction
      . apply ih h

lemma bindsConcatOk x τ (Γ₁ Γ₂ : env) :
  binds x τ Γ₁ -> envOk (Γ₂ ++ Γ₁) -> binds x τ (Γ₂ ++ Γ₁) := by
  induction Γ₂
  case nil => simp; intros; assumption
  case cons b Γ' ih =>
    intro hbd H; cases H
    next y τ' hctx g =>
      simp at hctx
      by_cases hxy : x = y
      . simp [if_pos hxy]
        by_contra; apply g
        apply bindsInEnv y τ (Γ' ++ Γ₁)
        rw [← hxy]; apply ih <;> assumption
      . simp [if_neg hxy]; apply ih <;> assumption

lemma weakeningBind Γ₁ Γ₂ Γ₃ x τ:
  binds x τ (Γ₁ ++ Γ₃) →
  envOk (Γ₁ ++ Γ₂ ++ Γ₃) →
  binds x τ (Γ₁ ++ Γ₂ ++ Γ₃) := by
  intro hb hctx
  induction Γ₁
  case nil => simp at *; apply bindsConcatOk; assumption; assumption
  case cons hd tl ih =>
    simp; by_cases heq: (x = hd.1) <;> simp at hb;
    . simp [heq]; simp [heq] at hb; assumption
    . simp [if_neg heq]; simp at ih; apply ih;
      simp [heq] at hb; assumption;
      cases hctx; next hctx' _ => simp at hctx'; assumption

lemma inCtxNeg x Γ1 Γ2 :
  ¬ (inEnv x (Γ1 ++ Γ2)) → ¬ (inEnv x Γ1) ∧ ¬ (inEnv x Γ2) := by
  intro h; induction Γ1
  case nil => simp; simp at h; assumption
  case cons hd tl ih =>
    simp; simp at h; exact ⟨⟨h.1, (ih h.2).1⟩, (ih h.2).2⟩

lemma inEnvNegMid x y τ Γ1 Γ2 :
  ¬ (inEnv x (Γ1 ++ (y, τ) :: Γ2)) → ¬ (inEnv x (Γ1 ++ Γ2)) := by
  intro hctx; induction Γ1 <;> simp <;> simp at hctx
  case nil => exact hctx.2
  case cons hd tl ih => exact ⟨hctx.1, ih hctx.2⟩

lemma inCtxNeg' x y τ Γ1 Γ2 :
  ¬ (inEnv x (Γ1 ++ (y,τ) :: Γ2)) → x ≠ y := by
  intro hctx; let ⟨hc1, hc2⟩ := inCtxNeg x Γ1 ((y,τ) :: Γ2) hctx;
  by_contra; next heq => simp [heq] at hc2

lemma bindsEqMid x τ1 τ2 Γ1 Γ2 :
  binds x τ1 (Γ2 ++ (x, τ2) :: Γ1) →
  envOk (Γ2 ++ (x, τ2) :: Γ1) →
  τ1 = τ2 := by
  intro hbd hctx; induction Γ2
  case nil => simp at *; symm; assumption
  case cons hd tl ih =>
    cases hctx; next hd _ hbd' hctx' =>
      apply ih <;> simp at hbd';
      . by_cases heq: (x = hd);
        . simp; simp [heq] at hbd; simp at hctx'
          have hneq := inCtxNeg' hd x τ2 tl Γ1 hctx';
          symm at hneq; contradiction
        . simp [if_neg, heq] at hbd; simp; assumption
      . assumption

lemma bindsNeqRemoveMid x y τ1 τ2 Γ1 Γ2 :
  binds x τ1 (Γ2 ++ (y, τ2) :: Γ1) → x ≠ y →
  binds x τ1 (Γ2 ++ Γ1) := by
  intro hbd hneq; induction Γ2
  case nil => simp; simp at hbd; simp [if_neg hneq] at hbd; assumption
  case cons hd tl ih =>
    simp at *; by_cases hxhd: (x = hd.1)
    . simp [hxhd] at hbd ⊢; assumption
    . simp [if_neg hxhd] at hbd ⊢; apply ih; assumption

lemma ctxOkRemoveMid x τ Γ1 Γ2:
  envOk (Γ2 ++ (x, τ) :: Γ1) →
  envOk (Γ2 ++ Γ1) := by
  intro hctx; induction Γ2
  case nil => simp; simp at hctx; cases hctx; assumption
  case cons hd tl ih =>
    simp at hctx; cases hctx; next hd _ hctx' =>
    constructor; apply ih; assumption; simp; exact (inEnvNegMid _ _ _ _ _ hctx')

inductive hasType : env → tm → ty → Prop
| t_var : ∀ Γ x τ, envOk Γ → binds x τ Γ → hasType Γ (.fvar x) τ
| t_abs : ∀ (L : Finset ℕ) Γ t τ₁ τ₂,
  (∀ (x: ℕ), x ∉ L → hasType ((x, τ₁)::Γ) (substB t (.fvar x)) τ₂) →
  hasType Γ (.abs t) (ty.arrow τ₁ τ₂)
| t_app : ∀ Γ t₁ t₂ τ₁ τ₂,
  hasType Γ t₁ (.arrow τ₁ τ₂) →
  hasType Γ t₂ τ₁ →
  hasType Γ (.app t₁ t₂) τ₂

-- weakening of typing

lemma weakening'' : ∀ (Γ' Γ₂ Γ₃ : env) t τ,
  hasType Γ' t τ →
  (Γ₁ : env) → Γ' = Γ₁ ++ Γ₂ →
  envOk (Γ₁ ++ Γ₃ ++ Γ₂) →
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
    simp; apply envOk.envOK_cs; rw [<- List.append_assoc]; assumption
    intro hctx; exact (hx.2 ((memDomIffInEnv _ _).mpr hctx))
  case t_app Γ t1 t2 τ1 τ2 ty1 ty2 ih1 ih2 =>
    intros Γ₁ heq hctx; apply hasType.t_app
    exact (ih1 Γ₁ heq hctx); exact (ih2 Γ₁ heq hctx)

lemma weakening' : ∀ (Γ₁ Γ₂ Γ₃ : env) t τ,
  hasType (Γ₁ ++ Γ₃) t τ →
  envOk (Γ₁ ++ Γ₂ ++ Γ₃) →
  hasType (Γ₁ ++ Γ₂ ++ Γ₃) t τ := by
  intros Γ₁ Γ₂ Γ₃ t τ hty hctx
  apply weakening''; assumption; rfl; assumption

lemma weakening : ∀ Γ₁ Γ₂ t τ,
  hasType Γ₂ t τ →
  envOk (Γ₁ ++ Γ₂) →
  hasType (Γ₁ ++ Γ₂) t τ := by
  intro Γ₁ Γ₂ t τ hty hctx
  rw [<- List.nil_append (Γ₁ ++ Γ₂)]
  apply weakening' [] Γ₁ Γ₂ t τ hty
  simp; assumption

-- substitution lemma

lemma typingSubstVar Γ1 Γ2 u τ1 τ2 z x:
  binds x τ1 (Γ2 ++ (z, τ2)::Γ1) →
  envOk (Γ2 ++ (z, τ2)::Γ1) →
  hasType Γ1 u τ2 →
  hasType (Γ2 ++ Γ1) (substF z u (.fvar x)) τ1 := by
  intro bh hctx hty
  simp; by_cases h: x = z
  . rw [h] at bh;
    have heq : τ1 = τ2 := bindsEqMid z τ1 τ2 Γ1 Γ2 bh hctx;
    simp [h] at bh ⊢; rw [heq]; apply weakening; assumption
    apply ctxOkRemoveMid; assumption
  . rw [if_neg h]; constructor; apply ctxOkRemoveMid; assumption;
    apply bindsNeqRemoveMid; assumption; assumption

lemma typingLc Γ t τ : hasType Γ t τ → lc t := by
  intro ht; induction ht <;> constructor <;> assumption

lemma typingSubst'' Γ1 Γ2 e u τ1 τ2 x :
  hasType Γ2 e τ1 →
  ((Γ3 : env) → Γ2 = (Γ3 ++ (x, τ2) :: Γ1) →
  hasType (Γ3 ++ (x, τ2) :: Γ1) e τ1 →
  hasType Γ1 u τ2 →
  hasType (Γ3 ++ Γ1) (substF x u e) τ1) := by
  intro h1; induction h1
  case t_var Γ' x' τ' hctx bd =>
    intro Γ3 hg h2 h3; apply typingSubstVar; rw [hg] at bd;
    assumption; rw [hg] at hctx; assumption; assumption
  case t_abs L Γ t τ₁ τ₂ ih1 ih2 =>
    intro Γ3 hg h2 h3; apply hasType.t_abs (L ∪ (dom (Γ3 ++ Γ1)) ∪ {x})
    intro y hyn; rw [substOpenVar]; simp at hyn; push_neg at hyn;
    rw [← List.nil_append ((y, τ₁) :: (Γ3 ++ Γ1)), List.append_cons,
        List.nil_append, ← List.append_assoc]
    apply ih2 y hyn.1; simp; assumption
    rw [hg] at ih1; apply ih1; exact hyn.1; assumption
    simp at hyn; push_neg at hyn; exact hyn.2.2; apply typingLc; assumption
  case t_app Γ t1 t2 τ₁ τ₂ ht1 ht2 ih1 ih2 =>
    intro Γ3 hg h2 h3; apply hasType.t_app
    apply ih1; assumption; simp [<- hg]; assumption; assumption
    apply ih2; assumption; simp [<- hg]; assumption; assumption

lemma typingSubst' Γ1 Γ2 e u τ1 τ2 x :
  hasType (Γ2 ++ (x, τ2) :: Γ1) e τ1 →
  hasType Γ1 u τ2 →
  hasType (Γ2 ++ Γ1) (substF x u e) τ1 := by
  intro h1 h2; apply typingSubst''; apply h1; rfl; assumption; assumption

lemma typingSubst Γ e u τ1 τ2 x :
  hasType ((x, τ2) :: Γ) e τ1 →
  hasType Γ u τ2 →
  hasType Γ (substF x u e) τ1 := by
  intro h1 h2; rw [<- List.nil_append ((x, τ2)::Γ)] at h1;
  rw [<- List.nil_append Γ]; apply typingSubst' <;> assumption

-- contextual reduction

inductive value : tm → Prop
| v_abs : ∀ t, lc (.abs t) → value (.abs t)

inductive contract : tm → tm → Prop
| beta : ∀ t1 t2,
  lc (.abs t1) → value t2 → contract (.app (.abs t1) t2) (substB t1 t2)

inductive ctx : (tm → tm) → Prop
| ctx_appL : ∀ t2, ctx (λ t => .app t t2)
| ctx_appR : ∀ t1, ctx (λ t => .app (.abs t1) t)

inductive evCtx : (tm → tm) → Prop
| evCtx_nil : evCtx id
| evCtx_cons : ∀ k1 k2, ctx k1 -> evCtx k2 -> evCtx (k1 ∘ k2)

inductive step : tm → tm → Prop
| red : ∀ k e1 e2, evCtx k -> contract e1 e2 -> step (k e1) (k e2)

-- preservation

lemma preservation Γ t t' τ :
  hasType Γ t τ → step t t' → hasType Γ t' τ := by
  intro _ hs; revert τ; cases hs; case red k e1 e2 evCtx' c =>
  induction evCtx' <;> intro τ ht
  . simp at *; cases c; case beta t1 t2 lc' vt2 =>
    cases ht; case t_app τ ht2 ht1 =>
    cases ht1; next L htt1' =>
    let ⟨x, hx⟩ := pick_fresh t1 L
    simp at hx; rw [substIntro];
    apply typingSubst; apply htt1'; exact hx.1; assumption
    exact hx.2; apply typingLc; assumption
  . case evCtx_cons k1 k2 ctxK1 evCtxK2 ih =>
    cases ctxK1 <;> cases ht with | t_app _ _ _ _ _ ht1 ht2 =>
    simp at *; apply hasType.t_app;
    repeat (first | apply ih | assumption)

-- progress

lemma ctxStep k e1 e2 :
  ctx k -> step e1 e2 -> step (k e1) (k e2) := by
  intros hctx hs; rcases hs with ⟨k', e1', e2', _, _⟩
  apply step.red (fun x => k (k' x));
  constructor; repeat assumption

lemma progress' Γ e τ : Γ = [] → hasType Γ e τ → value e ∨ ∃ e', step e e' := by
  intro hmt ht; induction ht;
  case t_var hbd => simp at hbd; rw [hmt] at hbd; simp at hbd
  case t_abs htbd _ => left; constructor; constructor; intros; apply typingLc; apply htbd; assumption
  case t_app Γ t1 t2 τ1 τ2 ht1 ht2 ih1 ih2 =>
    right; simp [hmt] at ih1; simp [hmt] at ih2; cases ih1
    . next vt1 =>
      cases ih2
      . next vt2 => cases vt1; next t' lct' =>
        use (substB t' t2); apply (step.red _ _ _ evCtx.evCtx_nil);
        constructor; assumption; assumption
      . next st =>
        rcases st with ⟨t2', st⟩; rcases vt1 with ⟨t1', _⟩
        use (t1'.abs.app t2'); apply ctxStep; constructor; assumption
    . next st =>
      rcases st with ⟨t1', st⟩
      use (t1'.app t2); apply ctxStep (fun x => .app x t2); constructor; assumption

lemma progress e τ : hasType [] e τ → value e ∨ ∃ e', step e e' := by apply progress'; simp
