{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --universe-polymorphism #-}

module embedding where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; inspect)
open Eq.≡-Reasoning

open import Data.Sum
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Maybe
open import Data.List hiding (length)
open import Data.List.Membership.Propositional
open import Data.Bool hiding (_<_; _≤_)
open import Data.Unit hiding (_≤_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Function using (_$_)
open import Relation.Nullary
open import Agda.Primitive
open import Level using (_⊔_) renaming (suc to lsuc; zero to lzero)

TNat : Set
TNat = ℕ

tzero : TNat
tzero = 0

TMem : {ℓ0 ℓ1 ℓ2 : Level} (L : Set ℓ1) (U : Set ℓ2) → Set ((lsuc ℓ0) ⊔ ℓ1 ⊔ ℓ2)
TMem {ℓ0} L U = Σ[ α ∈ Set ℓ0 ] (L → α) × (α → U)

TSel : {ℓ0 ℓ1 ℓ2 : Level} {L : Set ℓ1} {U : Set ℓ2} (T : TMem {ℓ0} L U) → Set ℓ0
TSel T = proj₁ T

TMem-inject : {ℓ0 : Level} (T : Set ℓ0) → TMem T T
TMem-inject T = ⟨ T , ⟨ (λ x → x) , (λ x → x) ⟩ ⟩

intro : {ℓ0 ℓ1 ℓ2 : Level} (L : Set ℓ1) (U : Set ℓ2) (x : TMem {ℓ0} L U) (y : L) → TSel x
intro L U ⟨ T , ⟨ ↑ , ↓ ⟩ ⟩ y = ↑ y

elim : {ℓ0 ℓ1 ℓ2 : Level} (L : Set ℓ1) (U : Set ℓ2) (x : TMem {ℓ0} L U) (y : TSel x) → U
elim L U ⟨ T , ⟨ ↑ , ↓ ⟩ ⟩ y = ↓ y

elim-realz : {ℓ0 ℓ1 ℓ2 : Level} (L : Set ℓ1) (U : Set ℓ2) (x : TMem {ℓ0} L U) → (TSel x → U)
elim-realz L U ⟨ T , ⟨ ↑ , ↓ ⟩ ⟩ = ↓

nest : {ℓ : Level} (T : Set ℓ) → TMem {lsuc ℓ} (TMem T T) (TMem T T)
nest T = TMem-inject (TMem T T)

unnest : {ℓ : Level} (T : Set ℓ) → TSel {lsuc ℓ} (nest T)
unnest T = TMem-inject T
