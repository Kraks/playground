{-# OPTIONS --without-K --safe #-}

module cek where

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
  data Exp : Set

  Lambda = Var × Exp

  data Exp where
    Ref : Var → Exp
    Lam : Lambda → Exp
    App : Exp → Exp → Exp

open Lang
  
-- A CEK Abstract Machine semantics
module CEK where

  data Env : Set
  data Value : Set
  data Cont : Set
  data 𝑺 : Set

  data Env where
    [] : Env
    _↦_∷_ : Var → Value → Env → Env

  data Value where
    Clo : Lambda → Env → Value

  data Cont where
    HaltK : Cont
    ArgK  : Exp → Env → Cont → Cont
    AppK  : Lambda → Env → Cont → Cont
  
  data 𝑺 where
    State : Exp → Env → Cont → 𝑺 

  _‼_ : Env → Var → Maybe Value
  [] ‼ x = nothing
  (x' ↦ v ∷ ρ) ‼ x with x ≟ x'
  ... | yes _ = just v
  ... | no _ = ρ ‼ x

  ρ₀ : Env
  ρ₀ = []

  ρ₁ = 1 ↦ (Clo ⟨ 0 , Ref 0 ⟩ ρ₀) ∷ ρ₀

  step : 𝑺 → Maybe 𝑺
  step (State (Ref x) ρ κ) with ρ ‼ x
  ... | just (Clo l ρ') = just (State (Lam l) ρ' κ)
  ... | nothing = nothing
  step (State (Lam l) ρ (ArgK e ρ' κ)) = just (State e ρ' (AppK l ρ κ))
  step (State (Lam l) ρ (AppK ⟨ x , e ⟩ ρ' κ)) = just (State e (x ↦ Clo l ρ ∷ ρ') κ)
  step (State (App e₁ e₂) ρ κ) = just (State e₁ ρ (ArgK e₂ ρ κ))
  step _ = nothing

  isFinal : 𝑺 → Bool
  isFinal (State (Lam _) _ HaltK) = true 
  isFinal _ = false

  drive : ℕ → 𝑺 → Maybe (Maybe 𝑺)
  drive n s = if (isFinal s) then just (just s) else drive' n s
    where
      drive' : ℕ → 𝑺 → Maybe (Maybe 𝑺)
      drive' 0 _ = nothing
      drive' (suc n) s with step s
      ... | just s' = drive n s'
      ... | nothing = just nothing

  inject : Exp → 𝑺
  inject e = State e ρ₀ HaltK

  eval : ℕ → Exp → Maybe (Maybe 𝑺)
  eval n e = drive n (inject e)
