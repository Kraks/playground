module plfa.part1.Isomorphism where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- λ { P₁ → N₁; Pₙ → Nₙ }

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' (suc n) = suc (m +' n)

same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m zero rewrite +-identityʳ m = refl
same-app m (suc n) rewrite +-comm m (suc n) | +-comm n m = cong suc (same-app m n)

same : _+'_ ≡ _+_
same = extensionality λ x → extensionality λ x₁ → same-app x x₁

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

-- two sets are isomorphic if they are one-to-one correspondence

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x -- from is a left-inverse of to
    to∘from : ∀ (y : B) → to (from y) ≡ y -- to is a left-inverse of from

open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl {A} = record
  { to = λ a → a
  ; from = λ y → y
  ; from∘to = λ x → refl
  ; to∘from = λ y → refl
  }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record
  { to = from A≃B
  ; from = to A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans AB BC = record
  { to = to BC ∘ to AB
  ; from = from AB ∘ from BC
  ; from∘to = λ { x →
    begin
      from AB (from BC (to BC (to AB x)))
    ≡⟨ cong (from AB) (from∘to BC (to AB x)) ⟩
      from AB (to AB x)
    ≡⟨ from∘to AB x ⟩
      x
    ∎}
  ; to∘from = λ { y →
    begin
      to BC (to AB (from AB (from BC y)))
    ≡⟨ cong (to BC) (to∘from AB (from BC y)) ⟩
      to BC (from BC y)
    ≡⟨ to∘from BC y ⟩
      y
    ∎}
  }

module ≃-Reasoning where
  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin AB = AB

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ AB ⟩ BC = ≃-trans AB BC

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

-- Embedding: a weakening of isomorphism.
-- An embedding shows that the first type is included in the second;
-- or, there is a many-to-one correspondence between the second type and the first.

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

open _≲_

-- Embedding is reflexive and transitive, but not symmetric

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = record
  { to = λ x → x
  ; from = λ z → z
  ; from∘to = λ x → refl
  }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans AB BC = record
  { to = to BC ∘ to AB
  ; from = from AB ∘ from BC
  ; from∘to = λ { x →
    begin
      from AB (from BC (to BC (to AB x)))
    ≡⟨ cong (from AB) (from∘to BC (to AB x)) ⟩
      from AB (to AB x)
    ≡⟨ from∘to AB x ⟩
      x
    ∎}
  }

-- Embedding is anti-symmetric (weak from of anti-symmetric?)

≲-antisym : ∀ {A B : Set}
  → (AB : A ≲ B)
  → (BA : B ≲ A)
  → (to AB ≡ from BA)
  → (from AB ≡ to BA)
  → A ≃ B
≲-antisym AB BA to≡from from≡to = record
  { to = to AB
  ; from = from AB
  ; from∘to = from∘to AB
  ; to∘from = λ { y →
    begin
      to AB (from AB y)
    ≡⟨ cong (to AB) (cong-app from≡to y) ⟩
      to AB (to BA y)
    ≡⟨ cong-app to≡from (to BA y) ⟩
      from BA (to BA y)
    ≡⟨ from∘to BA y ⟩
      y
    ∎}
  }

module ≲-Reasoning where
  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercises

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B = record
  { to = to A≃B
  ; from = from A≃B
  ; from∘to = from∘to A≃B
  }

-- Equivalence of propositions

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record
  { to = λ z → z
  ; from = λ z → z
  }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym AB = record
  { to = from AB
  ; from = to AB
  }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans AB BC = record
  { to = to BC ∘ to AB
  ; from = from AB ∘ from BC
  }

-- Exercise Bin-embedding (TODO)
