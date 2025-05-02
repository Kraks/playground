{-# OPTIONS --guardedness #-}

module Coind where

open import Relation.Binary.PropositionalEquality
open import Data.Product

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

-- define a bisimilarity (equivalence) of a pair of Stream A
record _≈_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-≈ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

even : ∀ {A} → Stream A → Stream A
hd (even x) = hd x
tl (even x) = even (tl (tl x))

odd : ∀ {A} → Stream A → Stream A
odd x = even (tl x)

split : ∀ {A} → Stream A → Stream A × Stream A
split xs = even xs , odd xs

merge : ∀ {A} → Stream A × Stream A → Stream A
hd (merge (fst , snd)) = hd fst
tl (merge (fst , snd)) = merge (snd , tl fst)
