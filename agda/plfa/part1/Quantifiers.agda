module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality; ∀-extensionality; _∘_)

-- Universals

∀-distrib-× : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to = λ x → ⟨ (λ a → proj₁ (x a)) , (λ a → proj₂ (x a)) ⟩
  ; from = λ x x₁ → ⟨ (proj₁ x x₁) , (proj₂ x x₁) ⟩
  ; from∘to = λ x → refl
  ; to∘from = λ{ ⟨ f , g ⟩ → refl }
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ x₁) x = inj₁ (x₁ x)
⊎∀-implies-∀⊎ (inj₂ y) x = inj₂ (y x)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

Tri-iso : ∀ (B : Tri → Set) → ((x : Tri) → B x) ≃ (B aa × B bb × B cc)
Tri-iso B = record
  { to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
  ; from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ aa → a
            ; ⟨ a , ⟨ b , c ⟩ ⟩ bb → b
            ; ⟨ a , ⟨ b , c ⟩ ⟩ cc → c }
  ; from∘to = λ{ f → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl } }
  ; to∘from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ → refl }
  }

-- Existentials

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- an equivalent definition using record type

record Σ' (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

-- Products arise as a special case of existentials, where
-- the second component does not depend on a variable drawn
-- from the first component.

∃ : ∀ {A : Set} → (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  → C
∃-elim f ⟨ x , bx ⟩ = f x bx

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to = λ{ f ⟨ x , y ⟩ → f x y }
  ; from = λ{ f y → λ by → f ⟨ y , by ⟩ }
  ; from∘to = λ x → refl
  ; to∘from = λ y → extensionality λ{ ⟨ x , x₁ ⟩ → refl }
  }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { to = λ{ ⟨ a , inj₁ x ⟩ → inj₁ ⟨ a , x ⟩ ; ⟨ a , inj₂ y ⟩ → inj₂ ⟨ a , y ⟩ }
  ; from = λ{ (inj₁ ⟨ x , x₁ ⟩) → ⟨ x , inj₁ x₁ ⟩ ; (inj₂ ⟨ x , x₁ ⟩) → ⟨ x , inj₂ x₁ ⟩ }
  ; from∘to = λ{ ⟨ x , inj₁ x₁ ⟩ → refl ; ⟨ x , inj₂ y ⟩ → refl }
  ; to∘from = λ{ (inj₁ ⟨ x , x₁ ⟩) → refl ; (inj₂ ⟨ x , x₁ ⟩) → refl }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ bx , cx ⟩ ⟩ = ⟨ ⟨ x , bx ⟩ , ⟨ x , cx ⟩ ⟩

∃-⊎ : ∀ (B : Tri → Set) → ∃[ x ] B x ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ B = record
  { to = λ{ ⟨ aa , bx ⟩ → inj₁ bx ; ⟨ bb , bx ⟩ → inj₂ (inj₁ bx) ; ⟨ cc , bx ⟩ → inj₂ (inj₂ bx) }
  ; from = λ{ (inj₁ a) → ⟨ aa , a ⟩ ; (inj₂ (inj₁ b)) → ⟨ bb , b ⟩ ; (inj₂ (inj₂ c)) → ⟨ cc , c ⟩ }
  ; from∘to = λ{ ⟨ aa , x₁ ⟩ → refl ; ⟨ bb , x₁ ⟩ → refl ; ⟨ cc , x₁ ⟩ → refl }
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl }
  }

open import plfa.part1.Relations using (even; odd)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} → odd  n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even.zero = ⟨ zero , refl ⟩
even-∃ (even.suc x) with odd-∃ x
...                    | ⟨ x' , refl ⟩ = ⟨ suc x' , refl ⟩

odd-∃ (odd.suc x) with even-∃ x
...                  | ⟨ x' , refl ⟩ = ⟨ x' , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even.zero
∃-even ⟨ suc m , refl ⟩ = even.suc (∃-odd ⟨ m , refl ⟩)
∃-odd ⟨ m , refl ⟩ = odd.suc (∃-even ⟨ m , refl ⟩)

-- Exercise

∃-even' : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd'  : ∀ {n : ℕ} → ∃[ m ] (m * 2 + 1 ≡ n) →  odd n

postulate
  +-idʳ : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

∃-even' ⟨ zero , refl ⟩ = even.zero
∃-even' ⟨ suc m , refl ⟩ = even.suc (∃-odd' ⟨ m , aux m ⟩)
  where
    aux : ∀ (n : ℕ) → n * 2 + 1 ≡ n + suc (n + zero)
    aux zero = refl
    aux (suc n) rewrite +-suc n (suc (n + 0)) = cong (suc ∘ suc) (aux n)

∃-odd' ⟨ zero , refl ⟩ = odd.suc even.zero
∃-odd' ⟨ suc m , refl ⟩ = odd.suc (even.suc (∃-odd' ⟨ m , refl ⟩))

-- Exercise

-- ∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) ≃ (∃[ x ] B x → C)

∃-proj₁ : ∀ {A : Set} → {B : A → Set} → Σ A B → A
∃-proj₁ ⟨ x , x₁ ⟩ = x

∃-proj₂ : ∀ {A : Set} → {B : A → Set} → (s : Σ A B) → B (∃-proj₁ s)
∃-proj₂ ⟨ x , x₁ ⟩ = x₁

∃-+-≤-1 : ∀ (y z : ℕ) → y ≤ z → ∃[ x ] (x + y ≡ z)
∃-+-≤-1 zero z lt = ⟨ z , +-idʳ z ⟩
∃-+-≤-1 (suc y) (suc z) (_≤_.s≤s lt) = ⟨ x , aux ⟩
  where
    x : ℕ
    x = ∃-proj₁ (∃-+-≤-1 y z lt)
    rec : x + y ≡ z
    rec = ∃-proj₂ (∃-+-≤-1 y z lt)
    aux : x + suc y ≡ suc z
    aux rewrite +-suc x y = cong suc rec

-- Negation of an existential is isomorphic to the universal of a negation
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = record
  { to = λ ¬∃ a bx → ¬∃ ⟨ a , bx ⟩
  ; from = λ{ f ⟨ a , ba ⟩ → (f a) ba }
  ; from∘to = λ ¬∃ → extensionality λ{ ⟨ x , x₁ ⟩ → refl }
  ; to∘from = λ y → refl
  }

-- Exercise

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} → ∃[ x ] (¬ B x) → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , bx ⟩ f = bx (f x)

-- Exercise : Bin-isomorphism (TODO)
