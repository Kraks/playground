-- https://github.com/lives-group/red-black-trees-agda/blob/master/Extrinsic.agda

module Extrinsic where

open import Agda.Primitive
open import Data.Nat
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

data Ord : Set where
  LT : Ord
  EQ : Ord
  GT : Ord

module RBTree {Key : Set} (comp : Key → Key → Ord) (Val : Set) where
  data Color : Set where
    Red : Color
    Blk : Color

  data Tree : Set where
    Mt : Tree
    Nd : (Key × Val) → Color → Tree → Tree → Tree

  balance : (Key × Val) → Color → Tree → Tree → Tree
  balance kv Blk (Nd y Red (Nd x Red a b) c) d = Nd y Red (Nd x Blk a b) (Nd kv Blk c d)
  balance kv Blk (Nd x Red a (Nd y Red b c)) d = Nd y Red (Nd x Blk a b) (Nd kv Blk c d)
  balance kv Blk a (Nd z Red (Nd y Red b c) d) = Nd y Red (Nd kv Blk a b) (Nd z Blk c d)
  balance kv Blk a (Nd y Red b (Nd z Red c d)) = Nd y Red (Nd kv Blk a b) (Nd z Blk c d)
  balance kv c l r = Nd kv c l r

  ins : (Key × Val) → Tree → Tree
  ins kv Mt = Nd kv Red Mt Mt
  ins (k , v) (Nd (k' , v') c l r) with comp k k'
  ins (k , v) (Nd (k' , v') c l r) | LT = balance (k' , v') c (ins (k , v) l) r
  ins (k , v) (Nd (k' , v') c l r) | EQ = Nd (k , v) c l r
  ins (k , v) (Nd (k' , v') c l r) | GT = balance (k' , v') c l (ins (k , v) r)

  blacken-root : Tree → Tree
  blacken-root Mt = Mt
  blacken-root (Nd kv _ l r) = Nd kv Blk l r

  insert : (Key × Val) → Tree → Tree
  insert kv t = blacken-root (ins kv t)

  module BlackHeightTake1 where

    data Black-height : Tree → ℕ → Set where
      BH-Mt : Black-height Mt 1
      BH-Nd-Red : ∀ {n : ℕ} {l r : Tree} {kv : Key × Val}
        → Black-height l n
        → Black-height r n
        → Black-height (Nd kv Red l r) n
      BH-Nd-Blk : ∀ {n : ℕ} {l r : Tree} {kv : Key × Val}
        → Black-height l n
        → Black-height r n
        → Black-height (Nd kv Blk l r) (suc n)

    blacken-root-bh : ∀ (t : Tree) (n : ℕ)
      → Black-height t n
      → Σ[ m ∈ ℕ ] Black-height (blacken-root t) m
    blacken-root-bh Mt n bh = 1 , BH-Mt
    blacken-root-bh (Nd x Red l r) n (BH-Nd-Red bh bh₁) = suc n , BH-Nd-Blk bh bh₁
    blacken-root-bh (Nd x Blk l r) (suc n) (BH-Nd-Blk bh bh₁) = suc n , BH-Nd-Blk bh bh₁

  module BlackHeightTake2 where

    data Color-height : Color → ℕ → ℕ → Set where
      CH-Red : ∀ {n : ℕ} → Color-height Red n n
      CH-Blk : ∀ {n : ℕ} → Color-height Blk n (suc n)

    data Black-height : Tree → ℕ → Set where
      BH-Mt : Black-height Mt 1
      BH-Nd : ∀ {m n : ℕ} {c : Color} {l r : Tree} {kv : Key × Val}
        → Black-height l n
        → Black-height r n
        → Color-height c n m
        → Black-height (Nd kv c l r) m

    blacken-root-bh : ∀ (t : Tree) (n : ℕ)
      → Black-height t n
      → Σ[ m ∈ ℕ ] Black-height (blacken-root t) m
    blacken-root-bh Mt n bh = n , bh
    blacken-root-bh (Nd x x₁ t t₁) n (BH-Nd l r ch) = _ , BH-Nd l r CH-Blk

  module BalanceTake where
    open BlackHeightTake2

    balance-bh : ∀ {l r : Tree} {c : Color} {kv : Key × Val} {n m : ℕ}
      → Black-height l n
      → Black-height r n
      → Color-height c n m
      → Black-height (balance kv c l r) m
    balance-bh hl hr c = {!!}

  ⋆
