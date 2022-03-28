{-# OPTIONS --without-K --safe #-}

module split_combine where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; inspect)
open Eq.≡-Reasoning

open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe
open import Data.List hiding (length)
open import Data.List.Membership.Propositional
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Unit hiding (_≤_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

split : ∀ {X Y : Set} (l : List (X × Y)) → (List X) × (List Y)
split [] = ⟨ [] , [] ⟩
split (⟨ a , b ⟩ ∷ l) = ⟨ a ∷ proj₁ (split l) , b ∷ proj₂ (split l) ⟩

combine : ∀ {X Y : Set} (xs : List X) → (ys : List Y) → List (X × Y)
combine [] ys = []
combine xs [] = []
combine (x ∷ xs) (y ∷ ys) = ⟨ x , y ⟩ ∷ combine xs ys

combine-split : ∀ {X Y : Set} (l : List (X × Y))
  → (l1 : List X) → (l2 : List Y)
  → split l ≡ ⟨ l1 , l2 ⟩
  → combine l1 l2 ≡ l
combine-split [] [] [] refl = refl
combine-split (⟨ x , y ⟩ ∷ l) .(x ∷ proj₁ (split l)) .(y ∷ proj₂ (split l)) refl =
  cong (λ l → ⟨ x , y ⟩ ∷ l) (combine-split l (proj₁ (split l)) (proj₂ (split l)) refl)

and≡or : ∀ (b c : Bool) (h : b ∧ c ≡ b ∨ c) → b ≡ c
and≡or false c h = h
and≡or true c h = sym h
