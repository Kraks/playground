{-# OPTIONS --without-K --safe #-}

module StackMachine where

open import Data.Nat
open import Data.Maybe
open import Data.List
open import Data.List.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; inspect)

-- Source Language

data op : Set where
  plus : op
  times : op

data exp : Set where
  const : ℕ → exp
  binop : op → exp → exp → exp

⟦_⟧ₒₚ : op → ℕ → ℕ → ℕ
⟦ plus ⟧ₒₚ a b = a + b
⟦ times ⟧ₒₚ a b = a * b

⟦_⟧ₑ : exp → ℕ
⟦ const x ⟧ₑ = x
⟦ binop op e₁ e₂ ⟧ₑ = ⟦ op ⟧ₒₚ ⟦ e₁ ⟧ₑ ⟦ e₂ ⟧ₑ

-- Target Language

data instr : Set where
  i-const : ℕ → instr
  i-binop : op → instr

prog : Set
prog = List instr

stack : Set
stack = List ℕ

⟦_⟧ᵢ : instr → stack → Maybe stack
⟦ i-const n ⟧ᵢ s = just (n ∷ s)
⟦ i-binop op ⟧ᵢ (x ∷ y ∷ s') = just (⟦ op ⟧ₒₚ x y ∷ s')
⟦ i-binop op ⟧ᵢ _ = nothing

⟦_⟧ₚ : prog → stack → Maybe stack
⟦ [] ⟧ₚ s = just s
⟦ i ∷ p' ⟧ₚ s with ⟦ i ⟧ᵢ s
... | nothing = nothing
... | just s' = ⟦ p' ⟧ₚ s'

-- Translation

compile : exp → prog
compile (const x) = [ i-const x ]
compile (binop op e₁ e₂) = compile e₂ ++ compile e₁ ++ [ i-binop op ]

compile-correct' : ∀ (e : exp) (p : prog) (s : stack) →
  ⟦ compile e ++ p ⟧ₚ s ≡ ⟦ p ⟧ₚ (⟦ e ⟧ₑ ∷ s)
compile-correct' (const x) p s = refl
compile-correct' (binop op e₁ e₂) p s
  rewrite ++-assoc (compile e₂) (compile e₁ ++ i-binop op ∷ []) p
        | ++-assoc (compile e₁) (i-binop op ∷ []) p
        | compile-correct' e₂ (compile e₁ ++ i-binop op ∷ p) s
        | compile-correct' e₁ (i-binop op ∷ p) (⟦ e₂ ⟧ₑ ∷ s)
  = refl

compile-correct : ∀ (e : exp) → ⟦ compile e ⟧ₚ [] ≡ just [ ⟦ e ⟧ₑ ]
compile-correct e rewrite sym (++-identityʳ (compile e)) = compile-correct' e [] []
