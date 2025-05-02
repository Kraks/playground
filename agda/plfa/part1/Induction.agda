module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = begin (3 + 4) + 5
    ≡⟨⟩ 7 + 5
    ≡⟨⟩ 12
    ≡⟨⟩ 3 + 9
    ≡⟨⟩ 3 + (4 + 5)
    ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin (zero + n) + p
  ≡⟨⟩ n + p
  ≡⟨⟩ zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-idʳ : ∀ (m : ℕ) → m + zero ≡ m
+-idʳ zero = refl
+-idʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-idʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin
    m + zero ≡⟨ +-idʳ m ⟩
    m        ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) = begin
    m + (suc n) ≡⟨ +-suc m n ⟩
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero    n p                        = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-id' : ∀ (n : ℕ) → n + zero ≡ n
+-id' zero = refl
+-id' (suc n) rewrite (+-id' n) = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite (+-suc' m n) = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-id' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

-- Exercise

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite +-swap m n p | +-suc n (m + p) = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-zero : ∀ (n : ℕ) → 0 ≡ n * 0
*-zero zero = refl
*-zero (suc n) = *-zero n

*-n-suc-m : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-n-suc-m zero n = refl
*-n-suc-m (suc m) n rewrite *-n-suc-m m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n = *-zero n
*-comm (suc m) n rewrite *-n-suc-m n m | *-comm m n = refl

zero-min : ∀ (n : ℕ) → zero ∸ n ≡ zero
zero-min zero = refl
zero-min (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero zero p = refl
∸-+-assoc zero (suc n) p = zero-min p
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

^-distrib-+ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distrib-+ zero zero p rewrite +-idʳ (zero ^ p) = refl
^-distrib-+ zero (suc n) p = refl
^-distrib-+ (suc m) zero p rewrite +-idʳ (suc m ^ p) = refl
^-distrib-+ (suc m) (suc n) p rewrite ^-distrib-+ (suc m) n p
                                    | *-distrib-+ (suc m ^ n) (m * (suc m ^ n)) (suc m ^ p)
                                    | *-assoc m (suc m ^ n) (suc m ^ p)
                                     = refl

*-swap : ∀ m n p → m * (n * p) ≡ n * (m * p)
*-swap zero n p = *-zero n
*-swap (suc m) n p rewrite *-comm n (p + m * p)
                         | *-distrib-+ p (m * p) n
                         | *-comm n p
                         | *-assoc m p n = refl

^-distrib-* : ∀ m n p → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distrib-* m n zero = refl
^-distrib-* m n (suc p) rewrite ^-distrib-* m n p
                              | *-assoc m n ((m ^ p) * (n ^ p))
                              | *-assoc m (m ^ p) (n * (n ^ p))
                              | *-swap n (m ^ p) (n ^ p) = refl

^-id : ∀ n → 1 ^ n ≡ 1
^-id zero = refl
^-id (suc n) rewrite +-idʳ (1 ^ n) = ^-id n

*-id : ∀ n → n ≡ 1 * n
*-id zero = refl
*-id (suc n) = cong suc (*-id n)

-- FIXME: give me a proper name
^-assoc : ∀ m n p → m ^ (n * p) ≡ (m ^ n) ^ p
^-assoc zero zero p rewrite ^-id p = refl
^-assoc zero (suc n) zero = ^-assoc zero n zero
^-assoc zero (suc n) (suc p) = refl
^-assoc (suc m) zero p rewrite ^-id p = refl
^-assoc (suc m) (suc n) p =
  begin
    suc m ^ (p + n * p)
  ≡⟨ ^-distrib-+ (suc m) p (n * p) ⟩
    (suc m ^ p) * (suc m ^ (n * p))
  ≡⟨ cong ((suc m ^ p) *_) (^-assoc (suc m) n p) ⟩
    (suc m ^ p) * ((suc m ^ n) ^ p)
  ≡⟨ sym (^-distrib-* (suc m) (suc m ^ n) p) ⟩
    (suc m * (suc m ^ n)) ^ p
  ≡⟨⟩
    ((1 + m) * (suc m ^ n)) ^ p
  ≡⟨ cong (_^ p) (*-distrib-+ 1 m (suc m ^ n)) ⟩
    (1 * (suc m ^ n) + m * (suc m ^ n)) ^ p
  ≡⟨ cong (λ v → (v + m * (suc m ^ n)) ^ p) (sym (*-id (suc m ^ n))) ⟩
    ((suc m ^ n) + m * (suc m ^ n)) ^ p
  ≡⟨⟩
    ((suc m) ^ (suc n)) ^ p
  ∎

-- TODO: Exercise Bin-laws (stretch)
