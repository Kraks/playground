module SystemF where

-- System F in Agda, for Fun and Profit
-- Chapman, Kireev, Nester, and Walder
-- URL: https://github.com/input-output-hk/plutus/blob/f9f7aef94d9614b67c037337079ad89329889ffa/papers/system-f-in-agda/paper.lagda

open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality
  using (subst; _≡_; refl; cong; cong₂; trans; sym)
open import Data.Sum as Sum renaming (inj₁ to inl; inj₂ to inr) 
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin

infix  4 _∋⋆_
infix  4 _⊢⋆_
infixl 5 _,⋆_

infix  6 Π
infixr 7 _⇒_

infix  5 ƛ
infixl 7 _∙_
infix  9 S

-- Kinds
-- K, J range over kinds

data Kind : Set where
  * : Kind
  _⇒_ : Kind → Kind → Kind

-- Type contexts
-- Φ, Ψ range over type contexts

data Ctx⋆ : Set where
  ∅ : Ctx⋆
  _,⋆_ : Ctx⋆ → Kind → Ctx⋆

-- Type variables, use de Bruijn indices
-- α, β range over type variables

data _∋⋆_ : Ctx⋆ → Kind → Set where
  Z : ∀ {Φ J} → Φ ,⋆ J ∋⋆ J
  S : ∀ {Φ J K}
    → Φ ∋⋆ J
    → Φ ,⋆ K ∋⋆ J

-- Types

data _⊢⋆_ (Φ : Ctx⋆) : Kind → Set where
  ` : ∀ {J} -- type variable
    → Φ ∋⋆ J
    → Φ ⊢⋆ J
  ƛ : ∀ {K J} -- type lambda
    → Φ ,⋆ K ⊢⋆ J
    → Φ ⊢⋆ K ⇒ J
  _∙_ : ∀ {K J} -- type application
      → Φ ⊢⋆ K ⇒ J
      → Φ ⊢⋆ K
      → Φ ⊢⋆ J
  _⇒_ : Φ ⊢⋆ * -- function type
      → Φ ⊢⋆ *
      → Φ ⊢⋆ *
  Π : ∀ {K} -- forall type
    → Φ ,⋆ K ⊢⋆ *
    → Φ ⊢⋆ *
  μ : Φ ,⋆ * ⊢⋆ *
    → Φ ⊢⋆ *

-- Type renaming

Ren⋆ : Ctx⋆ → Ctx⋆ → Set
Ren⋆ Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J

lift⋆ : ∀ {Φ Ψ} → Ren⋆ Φ Ψ → ∀ {K : Kind} → Ren⋆ (Φ ,⋆ K) (Ψ ,⋆ K)
lift⋆ ρ Z = Z           -- leave newly bound variable untouched
lift⋆ ρ (S α) = S (ρ α) -- apply renaming to other variables and add 1


