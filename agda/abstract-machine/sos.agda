{-# OPTIONS --without-K --safe #-}

module sos where

open import Data.Sum
open import Data.Nat
open import Data.Maybe
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Data.List hiding (length)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; inspect)

module Lang where
  Var = ℕ
  data Exp : Set where
    Ref : Var → Exp
    Lam : Exp → Exp
    App : Exp → Exp → Exp

open Lang

-- A structural small-step operational semantics
module SoS where

  data isValue : Exp → Set where
    Value-Lam : ∀ {e} → isValue (Lam e)

  -- d-place shift of an Exp above cutoff c
  shift : Exp → ℕ → ℕ → Exp
  shift (Ref k) d c with (k <? c)
  ...                  | yes k<c = Ref c
  ...                  | no  k≥c = Ref (k + d) 
  shift (Lam e) d c = Lam (shift e d (c + 1))
  shift (App e₁ e₂) d c = App (shift e₁ d c) (shift e₂ d c)

  shift0 : Exp → ℕ → Exp
  shift0 e d = shift e d 0

  [_↦_]_ : ℕ → Exp → Exp → Exp
  [ j ↦ s ] Ref x with j ≟ x
  ... | yes _ = s 
  ... | no _  = Ref x
  [ j ↦ s ] Lam e = Lam ([ j + 1 ↦ shift0 s 1 ] e)
  [ j ↦ s ] App e₁ e₂ = App ([ j ↦ s ] e₁) ([ j ↦ s ] e₂)

  data _⟶_ : Exp → Exp → Set where
    App₁ : ∀ {e₁ e₁' e₂}
      → e₁ ⟶ e₁'
      → App e₁ e₂ ⟶ App e₁' e₂
    App₂ : ∀ {e₁ e₂ e₂'}
      → e₂ ⟶ e₂'
      → App e₁ e₂ ⟶ App e₁ e₂'
    Beta : ∀ {v e}
      → isValue v
      → App (Lam e) v ⟶ ([ 0 ↦ v ] e) -- not entirely right


