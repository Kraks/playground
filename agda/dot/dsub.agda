{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --universe-polymorphism #-}

module dsub where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; inspect)
open Eq.≡-Reasoning

open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe
open import Data.List hiding (length)
open import Data.List.Membership.Propositional
open import Data.Bool hiding (_<_; _≤_)
open import Data.Unit hiding (_≤_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)

open import Function using (_$_)
open import Relation.Nullary
open import Agda.Primitive
open import Level renaming (suc to lsuc; zero to lzero)

id : Set
id = ℕ

data var : Set where
  var-f : id → var {- free, in cocnrete environment -}
  var-h : id → var {- free, in abstract environment -}
  var-b : id → var {- locally-bound variable -}

data ty : Set where
  dty-⊤ : ty
  dty-⊥ : ty
  dty-∀ : ty → ty → ty   {- (z: T) → Tᶻ -}
  dty-sel : var → ty     {- x.Type -}
  dty-mem : ty → ty → ty {- Type: S..U -}

data tm : Set where
  tvar : id → tm
  ttyp : ty → tm
  tabs : ty → tm → tm
  tapp : tm → tm → tm

data val : Set

tenv = List ty
venv = List val

length : ∀ {n : Level} {X : Set n} (xs : List X) → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

_⇓_ : ∀ {X : Set} (xs : List X) (n : ℕ) → Maybe X
[]       ⇓ n = nothing
(x ∷ xs) ⇓ n = if n ≡ᵇ (length xs) then just x else xs ⇓ n

-- TODO?
-- closed k j H T ensures that T is well-bound in a context H,
-- abstract environment J and under at most k binders.

data closed : (B : ℕ) → (H : ℕ) → (F : ℕ) → ty → Set where
  cl-⊤ : ∀ i j k → closed i j k dty-⊤
  cl-⊥ : ∀ i j k → closed i j k dty-⊥
  cl-∀ : ∀ i j k T1 T2
    → closed i       j k T1
    → closed (suc i) j k T2
    → closed i       j k (dty-∀ T1 T2)
  cl-sel-f : ∀ i j k x
    → k > x
    → closed i j k (dty-sel (var-f x))
  cl-sel-h : ∀ i j k x
    → j > x
    → closed i j k (dty-sel (var-h x))
  cl-sel-b : ∀ i j k x
    → i > x
    → closed i j k (dty-sel (var-b x))
  cl-mem : ∀ i j k T1 T2
    → closed i j k T1
    → closed i j k T2
    → closed i j k (dty-mem T1 T2)

open-rec : ∀ (k : ℕ) (u : var) (τ : ty) → ty
open-rec k u dty-⊤ = dty-⊤
open-rec k u dty-⊥ = dty-⊥
open-rec k u (dty-∀ τ₁ τ₂) = dty-∀ (open-rec k u τ₁) (open-rec (suc k) u τ₂)
open-rec k u (dty-sel (var-f x)) = dty-sel (var-f x)
open-rec k u (dty-sel (var-h x)) = dty-sel (var-h x)
open-rec k u (dty-sel (var-b x)) = if k ≡ᵇ x then dty-sel u else dty-sel (var-b x)
open-rec k u (dty-mem τ₁ τ₂) = dty-mem (open-rec k u τ₁) (open-rec k u τ₂)

-- open-var defines a locally-nameless encoding w.r.t. var-b variables

open-var : (u : var) (τ : ty) → ty
open-var u τ = open-rec 0 u τ

-- locally-nameless encoding w.r.t. var-h variables

subst : ∀ (u : var) (τ : ty) → ty
subst u dty-⊤ = dty-⊤
subst u dty-⊥ = dty-⊥
subst u (dty-∀ τ₁ τ₂) = dty-∀ (subst u τ₁) (subst u τ₂)
subst u (dty-sel (var-f x)) = dty-sel (var-b x)
subst u (dty-sel (var-h x)) = dty-sel (var-h x)
subst u (dty-sel (var-b x)) = if x ≡ᵇ 0 then dty-sel u else dty-sel (var-h (x ∸ 1))
subst u (dty-mem τ₁ τ₂) = dty-mem (subst u τ₁) (subst u τ₂)

nonsubst : ∀ (T : ty) → Set
nonsubst dty-⊤ = ⊤
nonsubst dty-⊥ = ⊤
nonsubst (dty-∀ τ1 τ2) = nonsubst τ1 × nonsubst τ2
nonsubst (dty-sel (var-f x)) = ⊤
nonsubst (dty-sel (var-h x)) = ⊤
nonsubst (dty-sel (var-b x)) = ¬ (x ≡ 0)
nonsubst (dty-mem τ1 τ2) = nonsubst τ1 × nonsubst τ2

-- Environments are splitted into two, an abstract environment and a concrete
--    environment.
-- First one: concrete enviornment is used for looking up var-f variables, and
--   is extended during type assignment.
-- Second one: abstract enviornment is used for looking up var-h variables, and
--   is extended during subtyping.

-- G ︔ GH ⊢ T1 <: T2

data _︔_⊢_<:_ : tenv → tenv → ty → ty → Set where
  <:-⊤ : ∀ G GH T1
    → closed 0 (length GH) (length G) T1
    → G ︔ GH ⊢ T1 <: dty-⊤
  <:-⊥ : ∀ G GH T2
    → closed 0 (length GH) (length G) T2
    → G ︔ GH ⊢ dty-⊥ <: T2
  <:-mem : ∀ G GH S1 U1 S2 U2
    → G ︔ GH ⊢ U1 <: U2
    → G ︔ GH ⊢ S2 <: S1
    → G ︔ GH ⊢ (dty-mem S1 U2) <: (dty-mem S2 U2)
  <:-sel-1 : ∀  G GH TX T2 x
    → G ⇓ x ≡ just TX
    → closed 0 0 (length G) TX
    → G ︔ GH ⊢ TX <: (dty-mem dty-⊥ T2)
    → G ︔ GH ⊢ (dty-sel (var-f x)) <: T2
  <:-sel-2 : ∀ G GH TX T1 x
    → G ⇓ x ≡ just TX
    → closed 0 0 (length G) TX
    → G ︔ GH ⊢ TX <: (dty-mem T1 dty-⊤)
    → G ︔ GH ⊢ T1 <: (dty-sel (var-f x))
  <:-sel-x : ∀ G GH v x
    → G ⇓ x ≡ just v
    → G ︔ GH ⊢ (dty-sel (var-f x)) <: (dty-sel (var-f x))
  <:-sel-a1 : ∀ G GH TX T2 x
    → GH ⇓ x ≡ just TX
    → closed 0 x (length G) TX
    → G ︔ GH ⊢ TX <: (dty-mem dty-⊥ T2)
    → G ︔ GH ⊢ (dty-sel (var-h x)) <: T2
  <:-sel-a2 : ∀ G GH TX T1 x
    → GH ⇓ x ≡ just TX
    → closed 0 x (length G) TX
    → G ︔ GH ⊢ TX <: (dty-mem T1 dty-⊤)
    → G ︔ GH ⊢ T1 <: (dty-sel (var-h x))
  <:-sel-ax : ∀ G GH v x
    → GH ⇓ x ≡ just v
    → G ︔ GH ⊢ (dty-sel (var-h x)) <: (dty-sel (var-h x))
  <:-sel-∀ : ∀ G GH T1 T2 T3 T4 x
    → G ︔ GH ⊢ T3 <: T1
    → x ≡ length GH
    → closed 1 (length GH) (length G) T2
    → closed 1 (length GH) (length G) T4
    → G ︔ (T3 ∷ GH) ⊢ (open-var (var-h x) T2) <: (open-var (var-h x) T4)
    → G ︔ GH        ⊢ (dty-∀ T1 T2) <: (dty-∀ T3 T4)
  <:-trans : ∀ G GH T1 T2 T3
    → G ︔ GH ⊢ T1 <: T2
    → G ︔ GH ⊢ T2 <: T3
    → G ︔ GH ⊢ T1 <: T3

-- Typing assignment

data _⊢_∶_ : tenv → tm → ty → Set where
  ty-var : ∀ x Γ T1
    → Γ ⇓ x ≡ just T1
    → Γ ︔ [] ⊢ T1 <: T1
    → Γ ⊢ (tvar x) ∶ T1
  ty-typ : ∀ Γ T1
    → closed 0 0 (length Γ) T1
    → Γ ⊢ (ttyp T1) ∶ (dty-mem T1 T1)
  ty-app : ∀ Γ f x T1 T2
    → Γ ⊢ f ∶ (dty-∀ T1 T2)
    → Γ ⊢ x ∶ T1
    → closed 0 0 (length Γ) T2
    → Γ ⊢ (tapp f x) ∶ T2
  ty-dapp : ∀ Γ f x T1 T2 T
    → Γ ⊢ f ∶ (dty-∀ T1 T2)
    → Γ ⊢ (tvar x) ∶ T1
    → T ≡ open-var (var-f x) T2
    → closed 0 0 (length Γ) T
    → Γ ⊢ (tapp f (tvar x)) ∶ T
  ty-abs : ∀ Γ e T1 T2
    → (T1 ∷ Γ) ⊢ e ∶ (open-var (var-f (length Γ)) T2)
    → closed 0 0 (length Γ) (dty-∀ T1 T2)
    → Γ ⊢ (tabs T1 e) ∶ (dty-∀ T1 T2)
  ty-sub : ∀ Γ e T1 T2
    → Γ ⊢ e ∶ T1
    → Γ ︔ [] ⊢ T1 <: T2
    → Γ ⊢ e ∶ T2

-- Evaluation

data val where
  vabs : venv → ty → tm → val
  vtyp : venv → ty → val

timeout : Maybe (Maybe val)
timeout = nothing

rt-err : Maybe (Maybe val)
rt-err = just nothing

eval : ∀ (n : ℕ) (ρ : venv) (t : tm) → Maybe (Maybe val)
eval zero ρ t = nothing
eval (suc n) ρ (tvar x) = just $ ρ ⇓ x
eval (suc n) ρ (ttyp τ) = just $ just $ vtyp ρ τ
eval (suc n) ρ (tabs τ e) = just $ just $ vabs ρ τ e
eval (suc n) ρ (tapp e₁ e₂) with eval n ρ e₂ -- why e2 first?
eval (suc n) ρ (tapp e₁ e₂) | nothing = timeout
eval (suc n) ρ (tapp e₁ e₂) | just nothing = rt-err
eval (suc n) ρ (tapp e₁ e₂) | just (just v) with eval n ρ e₁
eval (suc n) ρ (tapp e₁ e₂) | just (just v) | nothing = timeout
eval (suc n) ρ (tapp e₁ e₂) | just (just v) | just nothing = rt-err
eval (suc n) ρ (tapp e₁ e₂) | just (just v) | just (just (vtyp _ _)) = rt-err
eval (suc n) ρ (tapp e₁ e₂) | just (just v) | just (just (vabs ρ' _ body)) = eval n (v ∷ ρ') body

tevaln : ∀ (ρ : venv) (t : tm) (v : val) → Set
tevaln ρ e v = Σ[ m ∈ ℕ ] ∀ (n : ℕ) → n > m → eval n ρ e ≡ just (just v)

-- Logical relations

tsize-flat : ∀ (T : ty) → ℕ
tsize-flat dty-⊤ = 1
tsize-flat dty-⊥ = 1
tsize-flat (dty-∀ T1 T2) = suc (tsize-flat T1 + tsize-flat T2)
tsize-flat (dty-sel _) = 1
tsize-flat (dty-mem T1 T2) = suc (tsize-flat T1 + tsize-flat T2)

open-preserves-size : ∀ T x j → tsize-flat T ≡ tsize-flat (open-rec j (var-h x) T)
open-preserves-size dty-⊤ x j = refl
open-preserves-size dty-⊥ x j = refl
open-preserves-size (dty-∀ T₁ T₂) x j
  with open-preserves-size T₁ x j | open-preserves-size T₂ x (suc j)
... | eq1 | eq2 rewrite eq1 | eq2 = refl
open-preserves-size (dty-sel (var-f x₁)) x j = refl
open-preserves-size (dty-sel (var-h x₁)) x j = refl
open-preserves-size (dty-sel (var-b x₁)) x j with j ≡ᵇ x₁
open-preserves-size (dty-sel (var-b x₁)) x j | false = refl
open-preserves-size (dty-sel (var-b x₁)) x j | true = refl
open-preserves-size (dty-mem T₁ T₂) x j
  with open-preserves-size T₁ x j | open-preserves-size T₂ x j
... | eq1 | eq2 rewrite eq1 | eq2 = refl

data bound : Set where
  ub : bound
  lb : bound

sel = List bound

-- Polarity of selector strings
pos : sel → Bool
pos [] = true
pos (ub ∷ s) = pos s
pos (lb ∷ s) = if pos s then false else true

-- Semantic types are sets of values, indexed by a list of lb/ub selectors
vset : Set₁
vset = val → sel → Set

-- Set inclusion, taking polarity into account
vt-⊆ : vset → vset → Set
vt-⊆ a b = ∀ (vy : val) (iy : sel)
  → if pos iy then (a vy iy → b vy iy)
              else (b vy iy → a vy iy)

-- Good bound
good-bounds : vset → Set
good-bounds jj = ∀ vp ip → jj vp ip → ∀ vy iy
  → if pos iy
       then (jj vy (ip ++ (lb ∷ iy)) → jj vy (ip ++ (ub ∷ iy)))
       else (jj vy (ip ++ (ub ∷ iy)) → jj vy (ip ++ (lb ∷ iy)))

-- Definition of semantic types : ⟦ T ⟧ = { v | ... }

val-type : List vset → List vset → val → ty → sel → Set₁
val-type ρ GH (vabs ρ' T0 e) (dty-∀ T1 T2) [] =
    closed 0 (length GH) (length ρ) T1
  × closed 1 (length GH) (length ρ) T2
  × ∀ (vx : val) (jj : vset)
      → jj vx []
      -- → vt-⊆ jj (λ (vy : val) (iy : sel) → val-type ρ GH vy T1 iy)
      → good-bounds jj
      -- → Σ[ v ∈ val ] (tevaln (vx ∷ ρ') e v × val-type ρ (jj ∷ GH) v (open-var (var-h (length GH)) T2) [])
val-type ρ GH v T i = ⊥
