open import Data.Sum
open import Data.Nat
open import Agda.Primitive

fresh : ℕ
fresh = {!!}

data Exp : Set where
  Var : ℕ → Exp
  Lam : ℕ → Exp → Exp
  App : Exp → Exp → Exp

data Typ : Set where
  Base : Typ
  Arrow : Typ → Typ → Typ
{-
module NBE_Explicit where

  ⟦_⟧ : Typ → Set
  ⟦ Base ⟧ = Exp
  ⟦ Arrow τ₁ τ₂ ⟧ = ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧

  reify : (t : Typ) → ⟦ t ⟧ → Exp
  reflect : (t : Typ) → Exp → ⟦ t ⟧

  reify Base e = e
  reify (Arrow τ₁ τ₂) f = Lam x (reify τ₂ (f (reflect τ₁ (Var x))))
    where x = fresh

  reflect Base e = e
  reflect (Arrow τ₁ τ₂) f = λ x → reflect τ₂ (App f (reify τ₁ x))
-}
