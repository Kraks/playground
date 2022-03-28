module Ind where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data _≤_ : (a b : Nat) → Set where
  0ltn : ∀ {n} → 0 ≤ n
  nltm : ∀ {n m} → n ≤ m → suc n ≤ suc m

2lt3 : 2 ≤ 3
2lt3 = nltm (nltm 0ltn)
-- to prove 2 ≤ 3, we need 1 ≤ 2
-- to prove 1 ≤ 2, we need 0 ≤ 1

3lt5 : 3 ≤ 5
3lt5 = nltm (nltm (nltm 0ltn))

le-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
le-trans 0ltn h2 = 0ltn
le-trans (nltm h1) (nltm h2) = nltm (le-trans h1 h2)

data ⊥ : Set where

false-prop : 1 ≡ 0 → ⊥
false-prop ()

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

4lt3 : 4 ≤ 3 → ⊥
4lt3 (nltm (nltm (nltm ())))

infix 3 ¬_
¬_ : ∀ {a} → Set a → Set a
¬_ P = P → ⊥

4lt3₁ : ¬(4 ≤ 3)
4lt3₁ = 4lt3

_≠_ : ∀ {a} {A : Set a} → A → A → Set a
x ≠ y = ¬ (x ≡ y)
