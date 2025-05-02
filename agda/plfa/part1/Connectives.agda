module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)

open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

-- Conjunction is product

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  = 1
×-count ⟨ true  , bb ⟩  = 2
×-count ⟨ true  , cc ⟩  = 3
×-count ⟨ false , aa ⟩  = 4
×-count ⟨ false , bb ⟩  = 5
×-count ⟨ false , cc ⟩  = 6

-- product is commutative up to isomorphism
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩}
  ; from = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from∘to = λ { ⟨ x , y ⟩ → refl }
  ; to∘from = λ { ⟨ x , y ⟩ → refl }
  }

-- associative up to isomorphism
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
  ; from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
  ; from∘to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
  ; to∘from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
  }

-- Exercise ⇔≃×

open _⇔_
⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to = λ { x → ⟨ (to x) , (from x) ⟩ }
  ; from = λ { x → record { to = proj₁ x; from = proj₂ x } }
  ; from∘to = λ x → refl
  ; to∘from = λ { ⟨ AB , BA ⟩ → refl }
  }

-- Truth is unit
-- There is an introduction rule, but no elimination rule.

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

-- unit is the identity of product up to isomorphism

⊤-idˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-idˡ = record
  { to = λ{ ⟨ _ , x ⟩ → x }
  ; from = λ{ x → ⟨ tt , x ⟩ }
  ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
  ; to∘from = λ{ y → refl }
  }

⊤-idʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-idʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-idˡ ⟩
    A
  ≃-∎

-- Disjunction is sum

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

-- applying the destructor to each of the constructor is the identity

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infix 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

-- Exercise

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
  ; from = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
  ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ x) → refl }
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ x) → refl }
  }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to = λ{ (inj₁ (inj₁ x)) → inj₁ x ;
            (inj₁ (inj₂ x)) → inj₂ (inj₁ x) ;
            (inj₂ x) → inj₂ (inj₂ x) }
  ; from = λ{ (inj₁ x) → inj₁ (inj₁ x) ;
              (inj₂ (inj₁ x)) → inj₁ (inj₂ x) ;
              (inj₂ (inj₂ x)) → inj₂ x }
  ; from∘to = λ{ (inj₁ (inj₁ x)) → refl ;
                 (inj₁ (inj₂ x)) → refl ;
                 (inj₂ x) → refl }
  ; to∘from = λ{ (inj₁ x) → refl ;
                 (inj₂ (inj₁ x)) → refl ;
                 (inj₂ (inj₂ x)) → refl }
  }

-- False is empty

data ⊥ : Set where

-- No introduction rule, but an elimination rule

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} → (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- Exercise

⊥-idˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-idˡ = record
  { to = λ{ (inj₂ x) → x }
  ; from = λ{ x → inj₂ x }
  ; from∘to = λ{ (inj₂ x) → refl }
  ; to∘from = λ{ y → refl }
  }

⊥-idʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-idʳ = record
  { to = λ{ (inj₁ x) → x }
  ; from = λ{ x → inj₁ x }
  ; from∘to = λ{ (inj₁ x) → refl }
  ; to∘from = λ{ y → refl }
  }

-- Implication is function

-- modus ponens
→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M

-- elimination followed by introduction is the identity
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record
  { to = λ{ f ⟨ a , b ⟩ → f a b }
  ; from = λ{ g a b → g ⟨ a , b ⟩ }
  ; from∘to = λ x → refl
  ; to∘from = λ y → extensionality λ{ ⟨ x , y ⟩ → refl }
  }

-- p ^ (n + m) ≡ p ^ n * p ^ m
-- (A ⊎ B) → C ≃ (A → C) × (B → C)
-- if either A holds or B holds implies C, then we have
-- A implies C and B implies C

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
  { to = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
  ; from = λ{ ⟨ g , h ⟩ (inj₁ x) → g x ; ⟨ g , h ⟩ (inj₂ x) → h x }
  ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ x) → refl } }
  ; to∘from = λ{ ⟨ x , x₁ ⟩ → refl }
  }

→-distrib→× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib→× = record
  { to = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from = λ{ ⟨ f , g ⟩ → λ x → ⟨ f x , g x ⟩ }
  ; from∘to = λ f → extensionality λ x → η-× (f x)
  ; to∘from = λ{ ⟨ f , g ⟩ → refl }
  }

-- Distribution

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to = λ{ ⟨ inj₁ x , c ⟩ → inj₁ ⟨ x , c ⟩
          ; ⟨ inj₂ x , c ⟩ → inj₂ ⟨ x , c ⟩ }
  ; from = λ{ (inj₁ ⟨ x , x₁ ⟩) → ⟨ inj₁ x , x₁ ⟩
            ; (inj₂ ⟨ x , x₁ ⟩) → ⟨ inj₂ x , x₁ ⟩ }
  ; from∘to = λ{ ⟨ inj₁ x , x₁ ⟩ → refl ; ⟨ inj₂ x , x₁ ⟩ → refl }
  ; to∘from = λ{ (inj₁ ⟨ x , x₁ ⟩) → refl ; (inj₂ ⟨ x , x₁ ⟩) → refl }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record
  { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
             ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩ }
  ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
               ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
               ; ⟨ inj₂ z , _      ⟩ → (inj₂ z) }
  ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
               ; (inj₂ z)         → refl }
  }

-- Exercise

-- weak distributive law
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , c ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , c ⟩ = inj₂ ⟨ x , c ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , x₁ ⟩) = ⟨ inj₁ x , inj₁ x₁ ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , x₁ ⟩) = ⟨ inj₂ x , inj₂ x₁ ⟩
