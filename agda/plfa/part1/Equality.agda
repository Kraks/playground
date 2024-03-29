module plfa.part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z = begin
  x ≡⟨ x≡y ⟩
  y ≡⟨ y≡z ⟩
  z
  ∎

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

postulate
  +-id : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-id m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Exercise: ≤-Reasoning

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

module ≤-Reasoning where
  
-- +-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
-- +-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n evmn rewrite +-comm m n = evmn

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' zero n rewrite +-id n = refl
+-comm' (suc m) n rewrite +-suc n m | +-comm' m n = refl

-- dot pattern
even-comm' : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm' m n evmn with   m + n  | +-comm m n
...                    | .(n + m) | refl = evmn

even-comm'' : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm'' m n = subst even (+-comm m n)

-- Leibniz equality: identiy of indiscernibles
--   two objects are equal if and only if they satisfy the same properties.
-- Spock's law:
--   a difference that makes no difference is no difference

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P px = y≐z P (x≐y P px)

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

sym-≐' : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐' {A} {x} {y} x≐y P = x≐y (λ z → (Pz : P z) → P x) (λ x → x)

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ {A} {x} {y} x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q a = x ≡ a
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

-- Universe polymorphism

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl' : x ≡' x

sym' : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡' y → y ≡' x
sym' refl' = refl'

_≐'_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐'_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) a = g (f a)
