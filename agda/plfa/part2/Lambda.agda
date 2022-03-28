module plfa.part2.Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])

open import plfa.part1.Isomorphism

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _∙_
infix  8 `suc_
infix  9 `_

-- Terms

data Term : Set where
  `_ : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _∙_ : Term → Term → Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_ : Id → Term → Term

-- Example terms

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ ` "n"
    |suc "m" ⇒ `suc (` "+" ∙ ` "m" ∙ ` "n") ]

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" ∙ (` "s" ∙ ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
    ` "m" ∙ ` "s" ∙ (` "n" ∙ ` "s" ∙ ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- Exercise

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case `"m"
    [zero⇒ `zero
    |suc "m" ⇒ (`"+" ∙ `"n" ∙ (`"*" ∙ `"m" ∙ `"n"))]

-- Values

data Value : Term → Set where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)
  V-zero : Value `zero
  V-suc  : ∀ {V} → Value V → Value (`suc V)

-- Substituion (only consider closed terms)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := z ] with x ≟ y
... | yes p = z
... | no ¬p = ` x
(ƛ x ⇒ e) [ y := z ] with x ≟ y
... | yes p = ƛ x ⇒ e
... | no ¬p = ƛ x ⇒ e [ y := z ]
(e1 ∙ e2) [ y := z ] = e1 [ y := z ] ∙ e2 [ y := z ]
`zero [ y := z ] = `zero
(`suc x) [ y := z ] = `suc x [ y := z ]
case x [zero⇒ e1 |suc x' ⇒ e2 ] [ y := z ] with x' ≟ y
... | yes p = case x [ y := z ] [zero⇒ e1 [ y := z ] |suc x' ⇒ e2 ]
... | no ¬p = case x [ y := z ] [zero⇒ e1 [ y := z ] |suc x' ⇒ e2 [ y := z ] ]
(μ x ⇒ e) [ y := z ] with x ≟ y
... | yes p = μ x ⇒ e
... | no ¬p = μ x ⇒ e [ y := z ]

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- Exercise _[_:=_]′ (stretch)
-- The definition of substitution above has three clauses (ƛ, case, and μ) that
-- invoke a with clause to deal with bound variables. Rewrite the definition to
-- factor the common part of these three clauses into a single function, defined
-- by mutual recursion with substitution.

-- Call-by-value reduction

infix 4 _↦_

data _↦_ : Term → Term → Set where
  ξ-∙₁ : ∀ {L L' M}
         → L ↦ L'
         → L ∙ M ↦ L' ∙ M
  ξ-∙₂ : ∀ {V M M'}
         → Value V
         → M ↦ M'
         → V ∙ M ↦ V ∙ M'
  β-ƛ : ∀ {x N V}
        → Value V
        → (ƛ x ⇒ N) ∙ V ↦ N [ x := V ]
  ξ-suc : ∀ {M M'}
          → M ↦ M'
          → `suc M ↦ `suc M'
  ξ-case : ∀ {x L L' M N}
           → L ↦ L'
           → case L  [zero⇒ M |suc x ⇒ N ] ↦
             case L' [zero⇒ M |suc x ⇒ N ]
  β-zero : ∀ {x M N}
           → case `zero [zero⇒ M |suc x ⇒ N ] ↦ M
  β-suc : ∀ {x V M N}
          → Value V
          → case `suc V [zero⇒ M |suc x ⇒ N ] ↦ N [ x := V ]
  β-μ : ∀ {x M}
        → μ x ⇒ M ↦ M [ x := μ x ⇒ M ]

-- deterministic: for any term, there is at most one other term to
-- which it reduces.

-- Reflexive and transitive closure

infix 2 _↠_
infix 1 begin_
infixr 2 _↦⟨_⟩_
infix 3 _∎

data _↠_ : Term → Term → Set where
  _∎ : ∀ M → M ↠ M
  _↦⟨_⟩_ : ∀ L {M N}
    → L ↦ M
    → M ↠ N
    → L ↠ N

begin_ : ∀ {M N} → M ↠ N → M ↠ N
begin mn = mn

merge : ∀ {A B C} → A ↠ B → B ↠ C → A ↠ C
merge (M ∎) (M ∎) = M ∎
merge (M ∎) (M ↦⟨ MN ⟩ MC) = M ↦⟨ MN ⟩ MC
merge (L ↦⟨ LM₁ ⟩ M₁M) (M ∎) = L ↦⟨ LM₁ ⟩ M₁M
merge (L ↦⟨ LM₁ ⟩ M₁M) (M ↦⟨ MM₂ ⟩ MC) = L ↦⟨ LM₁ ⟩ merge M₁M (M ↦⟨ MM₂ ⟩ MC)

merge-single-step : ∀ {L M N} → (LM : L ↦ M) → (MN : M ↠ N)
  → merge (L ↦⟨ LM ⟩ (M ∎)) MN ≡ (L ↦⟨ LM ⟩ MN)
merge-single-step LM (M ∎) = refl
merge-single-step LM (L ↦⟨ x ⟩ MN) = refl

-- Define reflexive and transitive closure directly.

data _↠'_ : Term → Term → Set where
  step' : ∀ {M N} → M ↦ N → M ↠' N
  refl' : ∀ {M} → M ↠' M
  trans' : ∀ {L M N} → L ↠' M → M ↠' N → L ↠' N

-- Exercise: ↠ embeds in ↠'

↠≲↠' : ∀ {A B} → A ↠ B ≲ A ↠' B
↠≲↠' = record
  { to = to
  ; from = from
  ; from∘to = from∘to
  }
  where
    to : ∀ {A B} → A ↠ B → A ↠' B
    from : ∀ {A B} → A ↠' B → A ↠ B
    from∘to : ∀ {A B} → (x : A ↠ B) → from (to x) ≡ x
    to (M ∎) = refl'
    to (L ↦⟨ L↦M ⟩ M↦N) = trans' (step' L↦M) (to M↦N)
    from (step' {M} {N} M↦N) = M ↦⟨ M↦N ⟩ N ∎
    from (refl' {M}) = M ∎
    from (trans' {L} {M} {N} LM MN) = merge (from LM) (from MN)
    from∘to (M ∎) = refl
    from∘to (L ↦⟨ LM ⟩ MN) rewrite from∘to MN = merge-single-step LM MN

confluence : ∀ (L M N : Term) → Set
confluence L M N = Σ[ P ∈ Term ] ((L ↠ M) × (L ↠ N) → (M ↠ P) × (N ↠ P))

diamond : ∀ (L M N : Term) → Set
diamond L M N = Σ[ P ∈ Term ] ((L ↦ M) × (L ↦ N) → (M ↠ P) × (N ↠ P))

deterministic : ∀ {L M N : Term} → Set
deterministic {L} {M} {N} = (L ↦ M) → (L ↦ N) → M ≡ N

-- Every deterministic relation satisfies the diamond property.
-- Every relation that satisfies the diamond property is confluent.

-- Types

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Context

infixl 5 _,_⦂_

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

-- Exercise

{-
Context-≃ : Context ≃ List (Id × Type)
Context-≃ = record
  { to = {!!}
  ; from = {!!}
  ; from∘to = {!!}
  ; to∘from = {!!}
  }
-}

-- Lookup

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A}
    → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A

-- Typing judgement

infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where
  -- axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x ⦂ A
  -- λ-intro
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B
  -- λ-elim
  _∙_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
    → Γ ⊢ L ∙ M ⦂ B
  -- ℕ-intro-1
  ⊢zero : ∀ {Γ}
    → Γ ⊢ `zero ⦂ `ℕ
  -- ℕ-intro-2
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
    → Γ ⊢ `suc M ⦂ `ℕ
  -- ℕ-elim
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A
  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
    → Γ ⊢ μ x ⇒ M ⦂ A

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` (S (λ()) Z) ∙ (⊢` (S (λ()) Z) ∙ ⊢` Z)))

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
  (⊢suc (⊢` ∋+ ∙ ⊢` ∋m′ ∙ ⊢` ∋n′)))))
  where
  ∋+  = (S (λ()) (S (λ()) (S (λ()) Z)))
  ∋m  = (S (λ()) Z)
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = (S (λ()) Z)

⊢2+2 : ∅ ⊢ plus ∙ two ∙ two ⦂ `ℕ
⊢2+2 = ⊢plus ∙ ⊢two ∙ ⊢two

-- Lookup is injective

∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z Z = refl
∋-injective Z (S neq x1B) = ⊥-elim (neq refl)
∋-injective (S neq x1A) Z = ⊥-elim (neq refl)
∋-injective (S x xA) (S x₁ xB) = ∋-injective xA xB

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero ∙ `suc `zero ⦂ A)
nope₁ (() ∙ _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" ∙ ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` x ∙ ⊢` y)) = contra (∋-injective x y)
  where
    contra : ∀ {A B} → ¬ (A ⇒ B ≡ A)
    contra ()
