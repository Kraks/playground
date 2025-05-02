module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s le) = le

inv-z≤s : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤s z≤n = refl

{-
Reflexivie: ∀ n, n ≤ n
Transitive: ∀ m n p, m ≤ n ∧ n ≤ p → m ≤ p
Anti-symmetric: ∀ m n, if m ≤ n and n ≤ m, then m ≡ n
Total: ∀ m n, either m ≤ n or n ≤ m
-}

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n np = z≤n
≤-trans (s≤s mn) (s≤s np) = s≤s (≤-trans mn np)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s mn) (s≤s nm) = cong suc (≤-antisym mn nm)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward mn = forward (s≤s mn)
... | flipped nm = flipped (s≤s nm)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero n = forward z≤n
≤-total′ (suc m) zero = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward mn) = forward (s≤s mn)
  helper (flipped nm) = flipped (s≤s nm)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p mn rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n mn

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q mn pq = ≤-trans (+-monoˡ-≤ m n p mn) (+-monoʳ-≤ n p q pq)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
   z<s : ∀ {n : ℕ} → zero < suc n
   s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

-- Exercise
<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s np) = z<s
<-trans (s<s mn) (s<s np) = s<s (<-trans mn np)

data Trichotomy (m n : ℕ) : Set where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

suc-eq : ∀ (m n : ℕ) → m ≡ n → suc m ≡ suc n
suc-eq m .m refl = refl

ℕ-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
ℕ-trichotomy zero zero = eq refl
ℕ-trichotomy zero (suc n) = lt z<s
ℕ-trichotomy (suc m) zero = gt z<s
ℕ-trichotomy (suc m) (suc n) with ℕ-trichotomy m n
... | lt m<n = lt (s<s m<n)
... | eq refl = eq refl
... | gt n<m = gt (s<s n<m)

+-monoʳ-< : ∀ (m n p : ℕ) → n < p → m + n < m + p
+-monoʳ-< zero n p mn = mn
+-monoʳ-< (suc m) n p mn = s<s (+-monoʳ-< m n p mn)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p mn rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n mn

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q mn pq = <-trans (+-monoˡ-< m n p mn) (+-monoʳ-< n p q pq)

suc≤-if-< : ∀ (m n : ℕ) → m < n → suc m ≤ n
suc≤-if-< zero    _        z<s     = s≤s z≤n
suc≤-if-< (suc m) (suc n) (s<s mn) = s≤s (suc≤-if-< m n mn)

<-if-suc≤ : ∀ (m n : ℕ) → suc m ≤ n → m < n
<-if-suc≤ zero (suc n) (s≤s mn) = z<s
<-if-suc≤ (suc m) (suc n) (s≤s sucmn) = s<s (<-if-suc≤ m n sucmn)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡e : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc x) en = suc (o+e≡e x en)

o+e≡e (suc x) en = suc (e+e≡e x en)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc {m₁} m') (suc {n₁} n') rewrite +-comm m₁ (suc n₁) = suc (suc (e+e≡e n' m'))

-- TODO: Exercise Bin-predicates (stretch)
