module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)

open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

-- Values do not reduce

V¬↦ : ∀ {M N} → Value M → ¬ (M ↦ N)
V¬↦ V-ƛ = λ ()
V¬↦ V-zero = λ ()
V¬↦ (V-suc VM) = λ{ (ξ-suc M↦N) → V¬↦ VM M↦N }

↦¬V : ∀ {M N} → M ↦ N → ¬ Value M
↦¬V M↦N VM = V¬↦ VM M↦N

-- Canonical Forms

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)
  C-zero : Canonical `zero ⦂ `ℕ
  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
    → Canonical `suc V ⦂ `ℕ

-- every closed, well-typed value is canonical.
canonical : ∀ {V A} → ∅ ⊢ V ⦂ A → Value V → Canonical V ⦂ A
canonical (⊢ƛ t) V-ƛ = C-ƛ t
canonical ⊢zero V-zero = C-zero
canonical (⊢suc t) (V-suc v) = C-suc (canonical t v)

-- if a term is canonical then it is a value and well-typed in the empty context.
value : ∀ {M A} → Canonical M ⦂ A → Value M
value (C-ƛ x) = V-ƛ
value C-zero = V-zero
value (C-suc v) = V-suc (value v)

typed : ∀ {M A} → Canonical M ⦂ A → ∅ ⊢ M ⦂ A
typed (C-ƛ x) = ⊢ƛ x
typed C-zero = ⊢zero
typed (C-suc c) = ⊢suc (typed c)

-- Progress: If ∅ ⊢ M ⦂ A, then either M is a value or there is an N s.t. M ↦ N

data Progress (M : Term) : Set where
  step : ∀ {N} → M ↦ N → Progress M
  done : Value M → Progress M

-- well-typed term progresses

progress : ∀ {M A} → ∅ ⊢ M ⦂ A → Progress M
progress (⊢ƛ t) = done V-ƛ
progress (⊢M ∙ ⊢N) with progress ⊢M
... | step M↦M' = step (ξ-∙₁ M↦M')
... | done VM with progress ⊢N
... | step N↦N' = step (ξ-∙₂ VM N↦N')
... | done VN with canonical ⊢M VM
... | C-ƛ x = step (β-ƛ VN)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M↦M' = step (ξ-suc M↦M')
... | done VM    = done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L↦L' = step (ξ-case L↦L')
... | done VL with canonical ⊢L VL
... | C-zero = step β-zero
... | C-suc c = step (β-suc (value c))
progress (⊢μ t) = step β-μ

postulate
  progress' : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M ↦ N)

-- Exercise

Progress-≃ : ∀ M → Progress M ≃ Value M ⊎ ∃[ N ](M ↦ N)
Progress-≃ M = record
  { to = λ
    { (step {N} x) → inj₂ ⟨ N , x ⟩
    ; (done x) → inj₁ x
    }
  ; from = λ
    { (inj₁ VM) → done VM
    ; (inj₂ ⟨ N , M↦N ⟩) → step M↦N
    }
  ; from∘to = λ
    { (step {N} x) → refl
    ; (done x) → refl
    }
  ; to∘from = λ{ (inj₁ VM) → refl ; (inj₂ ⟨ N , M↦N ⟩) → refl }
  }

-- Exercise

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? (⊢ƛ t) = yes V-ƛ
value? (t ∙ t₁) = no (λ ())
value? ⊢zero = yes V-zero
value? (⊢suc t) with value? t
value? (⊢suc t) | yes p = yes (V-suc p)
value? (⊢suc t) | no ¬p = no λ{ (V-suc x) → ¬p x}
value? (⊢case t t₁ t₂) = no (λ ())
value? (⊢μ t) = no (λ ())

-- Prelude to preservation

-- Renaming: every variable appears in Γ also appears with the same type in Δ.
--           then if any term is typable under Γ, it has the same type under Γ.

ext : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext p Z = Z
ext p (S neq g) = S neq (p g)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename p (⊢` x) = ⊢` (p x)
rename p (⊢ƛ ⊢N) = ⊢ƛ (rename (ext p) ⊢N)
rename p (⊢M ∙ ⊢N) = rename p ⊢M ∙ rename p ⊢N
rename p ⊢zero = ⊢zero
rename p (⊢suc ty) = ⊢suc (rename p ty)
rename p (⊢case ⊢L ⊢M ⊢N) = ⊢case (rename p ⊢L) (rename p ⊢M) (rename (ext p) ⊢N)
rename p (⊢μ ⊢M) = ⊢μ (rename (ext p) ⊢M)

-- Weaken lemma: a term which is well-typed in ∅ is also well-typed in anarbitrary context.

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename (λ {x} {A} ()) ⊢M

-- Drop lemma: a term which is well-typed in a context where the same variable appears twice
---            remains well-typed if we drop the shadowed occuurrence.

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename p ⊢M
  where
  p : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
    → Γ , x ⦂ B ∋ z ⦂ C
  p Z = Z
  p (S x≢x Z) = ⊥-elim (x≢x refl)
  p (S z≢x (S _ ∋z)) = S z≢x ∋z

-- Swap lemma: a term which is well-typed in a context remains well-typed if we swap two variables.

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} neq ⊢M = rename p ⊢M
  where
    p : ∀ {z C}
      → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
    p Z = S neq Z
    p (S x Z) = Z
    p (S z≢x (S z≢y ∋z)) = S z≢y (S z≢x ∋z)

-- Types are preserved by substitution:
subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes p = weaken ⊢V
... | no ¬p = ⊥-elim (¬p refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes p = ⊥-elim (x≢y p)
... | no ¬p = ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl = ⊢ƛ (drop ⊢N)
... | no ¬p = ⊢ƛ (subst ⊢V (swap ¬p ⊢N))
subst ⊢V (⊢L ∙ ⊢M) = subst ⊢V ⊢L ∙ subst ⊢V ⊢M
subst ⊢V ⊢zero = ⊢zero
subst ⊢V (⊢suc vN) = ⊢suc (subst ⊢V vN)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no ¬p = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap ¬p ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl = ⊢μ (drop ⊢M)
... | no ¬p = ⊢μ (subst ⊢V (swap ¬p ⊢M))

-- Preservation: If ∅ ⊢ M ⦂ A and M ↦ N, then ∅ ⊢ N ⦂ A

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M ↦ N
  → ∅ ⊢ N ⦂ A
preserve (⊢L ∙ ⊢M) (ξ-∙₁ L↦L') = preserve ⊢L L↦L' ∙ ⊢M
preserve (⊢L ∙ ⊢M) (ξ-∙₂ VL M↦M') = ⊢L ∙ preserve ⊢M M↦M'
preserve (⊢ƛ ⊢L ∙ ⊢M) (β-ƛ VV) = subst ⊢M ⊢L
preserve (⊢suc ⊢M) (ξ-suc M↦M') = ⊢suc (preserve ⊢M M↦M')
preserve (⊢case ⊢L ⊢M ⊢N) (ξ-case L↦L') = ⊢case (preserve ⊢L L↦L') ⊢M ⊢N
preserve (⊢case ⊢L ⊢M ⊢N) β-zero = ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc x) = subst ⊢V ⊢N
preserve (⊢μ ⊢M) β-μ = subst (⊢μ ⊢M) ⊢M

-- Evaluation

data Gas : Set where
  gas : ℕ → Gas

data Finished (N : Term) : Set where
  done : Value N → Finished N
  out-of-gas : Finished N

data Steps (L : Term) : Set where
  steps : ∀ {N} → L ↠ N → Finished N → Steps L

eval : ∀ {L A} → Gas → ∅ ⊢ L ⦂ A → Steps L
eval {L} (gas zero) t = steps (L ∎) out-of-gas
eval {L} (gas (suc x)) ⊢L with progress ⊢L
... | done VL = steps (L ∎) (done VL)
... | step L↦M with eval (gas x) (preserve ⊢L L↦M)
... | steps M↠N finish = steps (L ↦⟨ L↦M ⟩ M↠N) finish

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where ∋x = Z

r1 : Steps (μ "x" ⇒ `suc ` "x")
r1 = eval (gas 3) ⊢sucμ

-- Exercise subject-expansion
-- preservation property is also called subject reduction
-- its opposite is subject expansion:
-- if M ↦ N and ∅ ⊢ N ⦂ A, then ∅ ⊢ M ⦂ A
-- Counter-examples:
--   M = if true then 1 else 1 + Bool

-- Well-typed terms don't get stuck

Normal : Term → Set
Normal M = ∀ {N} → ¬ (M ↦ N)

Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

unstuck : ∀ {M A} → ∅ ⊢ M ⦂ A → ¬ (Stuck M)
unstuck (⊢ƛ t) = λ z → proj₂ z V-ƛ
unstuck (e1 ∙ e2) with progress (e1 ∙ e2)
... | step x = λ{ ⟨ norm , ¬val ⟩ → norm x }
unstuck ⊢zero = λ z → proj₂ z V-zero
unstuck (⊢suc t) with progress (⊢suc t)
unstuck (⊢suc t) | step x = λ z → proj₁ z x
unstuck (⊢suc t) | done x = λ z → proj₂ z x
unstuck (⊢case L M N) with progress L
unstuck (⊢case L M N) | step x = λ z → proj₁ z (ξ-case x)
unstuck (⊢case L M N) | done V-zero = λ z → proj₁ z β-zero
unstuck (⊢case L M N) | done (V-suc x) = λ z → proj₁ z (β-suc x)
unstuck (⊢μ t) = λ z → proj₁ z β-μ

preserves : ∀ {M N A} → ∅ ⊢ M ⦂ A → M ↠ N → ∅ ⊢ N ⦂ A
preserves ty-M (M ∎) = ty-M
preserves ty-L (L ↦⟨ x ⟩ MN) = preserves (preserve ty-L x) MN

wttdgs : ∀ {M N A} → ∅ ⊢ M ⦂ A → M ↠ N → ¬ (Stuck N)
wttdgs ty-M (M ∎) = unstuck ty-M
wttdgs ty-L (L ↦⟨ x ⟩ MN) with preserve ty-L x
... | p = wttdgs p MN

-- Reduction is determinisitc

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  → {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w
  → t ≡ x
  → u ≡ y
  → v ≡ z
  → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M M' M''} → (M ↦ M') → (M ↦ M'') → (M' ≡ M'')
det m1 m2 = {!!}
