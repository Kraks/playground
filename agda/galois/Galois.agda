module Galois where

open import Data.Sum
open import Data.Maybe
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.List hiding (length)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; inspect)

open import Level renaming (_⊔_ to _⊔ℓ_)

-- Modeling relations

_←_ : ∀ {i j k} → Set i → Set j → Set (suc k ⊔ℓ (j ⊔ℓ i))
_←_ {i} {j} {k} B A = B → A → Set k

_←_⊣_ : ∀ {i j} → Set i → Set j → (k : Level) → Set (suc k ⊔ℓ (j ⊔ℓ i))
B ← A ⊣ k = _←_ {k = k} B A


