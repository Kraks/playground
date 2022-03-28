module plfa.part1.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ b = true
suc a ≤ᵇ zero = false
suc a ≤ᵇ suc b = a ≤ᵇ b

_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true  tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n t = z≤n
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s l) = ≤→≤ᵇ l

-- The best of both worlds

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

-- Exercise

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s s) = ¬m<n s

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no λ ()
zero <? suc n = yes z<s
suc m <? zero = no λ ()
suc m <? suc n with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)

-- Exericse

¬≡ℕ : ∀ {m n : ℕ} → ¬ m ≡ n → ¬ (suc m) ≡ (suc n)
¬≡ℕ m≡n refl = m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc b = no (λ ())
suc a ≡ℕ? zero = no (λ ())
suc a ≡ℕ? suc b with a ≡ℕ? b
... | yes refl = yes refl
... | no neq = no (¬≡ℕ neq)

-- Decidables from booleans, and booleans from decidables

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _  = yes (p tt)
...        | false  | _        | ¬p = no ¬p

⌞_⌟ : ∀ {A : Set} → Dec A → Bool
⌞ yes p ⌟ = true
⌞ no ¬p ⌟ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  = ⌞ m ≤? n ⌟

toWitness : ∀ {A : Set} {D : Dec A} → T ⌞ D ⌟ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌞ D ⌟
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

-- Logical connectives

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true 
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ x → ¬x (proj₁ x)
_     ×-dec no ¬y = no λ x → ¬y (proj₂ x)

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec b = yes (inj₁ x)
no ¬x ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not  true = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no λ ¬a → ¬a x
¬? (no ¬x) = yes ¬x

_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
a →-dec yes x = yes (λ _ → x)
yes a →-dec no ¬b = no (λ a→b → ¬b (a→b a))
no ¬a →-dec no ¬b = yes λ a → ⊥-elim (¬a a)

-- Exercise

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ ∧ ⌞ y ⌟ ≡ ⌞ x ×-dec y ⌟
∧-× (yes a) (yes b) = refl
∧-× (yes a) (no ¬b) = refl
∧-× (no ¬a) b = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ ∨ ⌞ y ⌟ ≡ ⌞ x ⊎-dec y ⌟
∨-⊎ (yes x) b = refl
∨-⊎ (no ¬a) (yes b) = refl
∨-⊎ (no ¬a) (no ¬b) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌞ x ⌟ ≡ ⌞ ¬? x ⌟
not-¬ (yes x) = refl
not-¬ (no x) = refl

_iff_ : Bool → Bool → Bool
true  iff true  = true
false iff false = true
_     iff _     = false

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes (record { to = λ _ → b ; from = λ _ → a })
yes a ⇔-dec no ¬b = no λ{ record { to = to ; from = from } → ¬b (to a) }
no ¬a ⇔-dec yes b = no λ{ record { to = to ; from = from } → ¬a (from b) }
no ¬a ⇔-dec no ¬b = yes (record { to = λ a → ⊥-elim (¬a a); from = λ b → ⊥-elim (¬b b) })

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ iff ⌞ y ⌟ ≡ ⌞ x ⇔-dec y ⌟
iff-⇔ (yes x) (yes x₁) = refl
iff-⇔ (yes x) (no x₁) = refl
iff-⇔ (no x) (yes x₁) = refl
iff-⇔ (no x) (no x₁) = refl
