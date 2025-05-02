module plfa.part2.DeBruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)

-- de Bruijn indices

-- Syntax

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _∙_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Typing context

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

_ : Ctx
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ

data _∋_ : Ctx → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z

-- Terms and typing judgement

data _⊢_ : Ctx → Type → Set where
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B
  _∙_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B
  `zero : ∀ {Γ} → Γ ⊢ `ℕ
  `suc_ : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
    → Γ ⊢ A
  μ_ : ∀ {Γ A} → Γ , A ⊢ A → Γ ⊢ A

lookup : Ctx → ℕ → Type
lookup (Γ , A) zero = A
lookup (Γ , _) (suc n) = lookup Γ n
lookup ∅ _ = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero = Z
count {Γ , _} (suc n) = S (count n)
count {∅} _ = ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n = ` count n

-- Examples

two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ {-f-} ƛ {-m-} ƛ {-n-}
         (case (# 1) -- match m
               (# 0) -- if m ≡ 0, then n
               {-m'-} (`suc (# 3 ∙ # 0 ∙ # 1))) -- 1 + f m' n

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 ∙ (# 1 ∙ # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 ∙ # 1 ∙ (# 2 ∙ # 1 ∙ # 0))

-- Exercise: mul

-- Renaming

ext : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z = Z
ext ρ (S e) = S ρ e

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) = ` ρ x
rename ρ (ƛ t) = ƛ (rename (ext ρ) t)
rename ρ (t₁ ∙ t₂) = (rename ρ t₁) ∙ (rename ρ t₂)
rename ρ `zero = `zero
rename ρ (`suc t) = `suc (rename ρ t)
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ t) = μ (rename (ext ρ) t)


