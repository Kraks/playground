module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import plfa.part1.Isomorphism using (_≃_; extensionality; _≲_)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

-- A → (A → ⊥) → ⊥
¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro a x = x a

-- ((A → ⊥) → ⊥ → ⊥) → A → ⊥
¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim f a = f (¬¬-intro a)

-- (A → B) → (B → ⊥) → A → ⊥
contradiction : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contradiction f ¬b a = ¬b (f a)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- Exercise

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive (suc n) (s<s lt) = <-irreflexive n lt

-- Exercise
data Trichotomy (m n : ℕ) : Set where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

suc-eq : ∀ (m n : ℕ) → suc m ≡ suc n → m ≡ n
suc-eq m m refl = refl

suc-lt : ∀ (m n : ℕ) → suc n < suc m → n < m
suc-lt m n (s<s snsm) = snsm

exclusive-lt : ∀ (m n : ℕ) → (m < n) → (¬ m ≡ n × ¬ n < m)
exclusive-lt zero (suc _) z<s = ⟨ (λ ()) , (λ ()) ⟩
exclusive-lt (suc m) (suc n) (s<s mn) =
  ⟨ (λ sm≡sn → proj₁ (exclusive-lt m n mn) (suc-eq m n sm≡sn)) ,
    (λ sn<sm → proj₂ (exclusive-lt m n mn) (suc-lt m n sn<sm)) ⟩

exclusive-eq : ∀ (m n : ℕ) → m ≡ n → (¬ m < n × ¬ n < m)
exclusive-eq m n m≡n = ⟨ exclusive-eq-1 m n m≡n , exclusive-eq-2 m n m≡n ⟩
  where
  exclusive-eq-1 : ∀ (m n : ℕ) → m ≡ n → ¬ m < n
  exclusive-eq-1 (suc m) (suc n) refl (s<s m<n) = exclusive-eq-1 m n refl m<n
  exclusive-eq-2 : ∀ (m n : ℕ) → m ≡ n → ¬ n < m
  exclusive-eq-2 (suc m) (suc n) refl (s<s n<m) = exclusive-eq-2 m n refl n<m

exclusive-gt : ∀ (m n : ℕ) → n < m → (¬ m < n × ¬ m ≡ n)
exclusive-gt m n n<m = ⟨ exclusive-gt-1 m n n<m , exclusive-gt-2 m n n<m ⟩
  where
  exclusive-gt-1 : ∀ (m n : ℕ) → n < m → ¬ m < n
  exclusive-gt-1 (suc m) (suc n) (s<s n<m) (s<s m<n) = exclusive-gt-1 m n n<m m<n
  exclusive-gt-2 : ∀ (m n : ℕ) → n < m → ¬ m ≡ n
  exclusive-gt-2 (suc m) (suc n) (s<s n<m) refl = exclusive-gt-2 m n n<m refl

-- Exercise

demorgan-1 : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
demorgan-1 = record
  { to = λ{ f → ⟨ (λ a → f (inj₁ a)) , (λ b → f (inj₂ b)) ⟩ }
  ; from = λ{ ⟨ na , nb ⟩ (inj₁ x) → na x ; ⟨ na , nb ⟩ (inj₂ y) → nb y }
  ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
  ; to∘from = λ{ ⟨ na , nb ⟩ → refl }
  }

-- TODO:
-- demorgan-2 : ∀ {A B : Set} → ¬ (A × B) ≲ (¬ A) ⊎ (¬ B)

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

-- the negation of its negation is provable

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ λ a → k (inj₁ a))

-- Exercise

false→any : ∀ {A : Set} → ⊥ → A
false→any ()

-- Excluded middle implies Double Negation Elimination
em→dn : ∀ {A : Set} → (A ⊎ ¬ A) → (¬ ¬ A → A)
em→dn (inj₁ x) nna = x
em→dn (inj₂ y) nna = false→any (nna y)

dn→em : (∀ {A : Set} → (¬ ¬ A → A)) → {A : Set} → (A ⊎ ¬ A)
dn→em f = f em-irrefutable

-- Excluded middle implies Peirce's Law
em→peirce : ∀ {A B : Set} → (A ⊎ ¬ A) → (((A → B) → A) → A)
em→peirce (inj₁ x) aba = x
em→peirce (inj₂ y) aba = aba (λ x → false→any (y x))

peirce→em : (∀ {A B : Set} → ((A → B) → A) → A) → ∀ {A : Set} → (A ⊎ ¬ A)
peirce→em f = f (λ g → inj₂ (λ a → g (inj₁ a)))

-- Excluded middle implies Implication as Disjunction
em→iasd : ∀ {A B : Set} → (A ⊎ ¬ A) → ((A → B) → ¬ A ⊎ B)
em→iasd (inj₁ x) ab = inj₂ (ab x)
em→iasd (inj₂ y) ab = inj₁ y

iasd→em : (∀ {A B : Set} → ((A → B) → ¬ A ⊎ B)) → {A : Set} → (A ⊎ ¬ A)
iasd→em f = swap (f λ z → z)

-- Excluded middle implies De Morgan
em→dm : (∀ {A : Set} → (A ⊎ ¬ A)) → (∀ {B C : Set} → (¬ (¬ B × ¬ C) → B ⊎ C))
em→dm em {B} {C} nab with em {B}  | em {C}
em→dm em {B} {C} nab    | inj₁ b  | _       = inj₁ b
em→dm em {B} {C} nab    | inj₂ ¬b | inj₁ c  = inj₂ c
em→dm em {B} {C} nab    | inj₂ ¬b | inj₂ ¬c = ⊥-elim (nab ⟨ ¬b , ¬c ⟩)

dm→em : (∀ {A B : Set} → (¬ (¬ A × ¬ B) → A ⊎ B)) → {A : Set} → (A ⊎ ¬ A)
dm→em f = f λ x → proj₂ x (proj₁ x)

-- Exercise: Stable

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-Stable : ∀ {A : Set} → Stable (¬ A)
¬-Stable = ¬¬¬-elim

×-Stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-Stable as bs = λ ¬¬ab → ⟨ (as (λ z → ¬¬ab (λ z₁ → z (proj₁ z₁))))
                          , (bs (λ z → ¬¬ab (λ z₁ → z (proj₂ z₁)))) ⟩

data ¬'_ (A : Set) : Set where
  neg : (A → ⊥) → ¬' A

_ : ¬' (1 ≡ 2)
_ = neg (λ ())
