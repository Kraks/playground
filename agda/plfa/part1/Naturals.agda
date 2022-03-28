module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

seven : ℕ
seven = succ (succ (succ (succ (succ (succ (succ zero))))))

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

_ : 2 + 3 ≡ 5
_ = begin
    2 + 3
    ≡⟨⟩ succ (1 + 3)
    ≡⟨⟩ succ (succ (0 + 3))
    ≡⟨⟩ succ (succ 3)
    ≡⟨⟩ 5
    ∎

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ m) * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ = begin
    2 * 3
    ≡⟨⟩ 3 + (1 * 3)
    ≡⟨⟩ 3 + (3 + (0 * 3))
    ≡⟨⟩ 3 + (3 + 0)
    ≡⟨⟩ 6
    ∎

-- Exercise: exponentiation

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (succ m) = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ m = zero
succ m ∸ succ n = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ = refl

_ : 3 ∸ 5 ≡ 0
_ = refl

infixl 6 _+_ _∸_
infixl 8 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

_ : Bin
_ = ⟨⟩ I O I I -- 1011

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩
to (succ n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * (from b)
from (b I) = succ (2 * from b)

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

_ : from (⟨⟩ I O O I) ≡ 9
_ = refl

postulate
  add-0 : ∀ n → n + zero ≡ n
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  twice : ∀ n → n + n ≡ 2 * n

bin-law1 : ∀ b → from (inc b) ≡ succ (from b)
bin-law1 ⟨⟩ = refl
bin-law1 (b O) = refl
bin-law1 (b I) rewrite add-0 (from (inc b)) | add-0 (from b)
                     | bin-law1 b | +-comm (from b) (succ (from b)) = refl

-- bin-law2 : ∀ b → to (from b) ≡ b

¬bin-law2 : Σ[ n ∈ Bin ] ¬ (to (from n) ≡ n)
¬bin-law2 = ⟨ ⟨⟩ O , (λ ()) ⟩

bin-law3 : ∀ b → from (to b) ≡ b
bin-law3 zero = refl
bin-law3 (succ b) rewrite bin-law1 (to b) | bin-law3 b = refl
