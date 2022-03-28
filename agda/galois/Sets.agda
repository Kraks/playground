{-# OPTIONS --universe-polymorphism #-}

module Sets where

open import Data.Empty   using (⊥)
open import Relation.Unary public
  using (_∪_; _∩_)
  renaming (_⊆′_ to _⊆_; _⊇′_ to _⊇_)
open import Relation.Binary.PropositionalEquality
  public using  (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary
open import Data.Sum     using (_⊎_)
open import Data.Product using (_×_; _,_)
open import Level

ℙ : ∀ {ℓ : Level} → Set ℓ → Set (suc ℓ)
ℙ {ℓ} A = A → Set ℓ

⊆-refl : ∀ {ℓ} {A : Set ℓ} → {r : ℙ A} → r ⊆ r
⊆-refl _ ra = ra

⊆-trans : ∀ {ℓ} {A : Set ℓ} → {r s t : ℙ A}
  → r ⊆ s → s ⊆ t → r ⊆ t
⊆-trans r⊆s s⊆t a a∈r = s⊆t a (r⊆s a a∈r)
