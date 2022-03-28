{-# OPTIONS --without-K --safe #-}

module stlc_op where

open import Data.Sum
open import Data.Nat
open import Data.Maybe
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.List hiding (length)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; inspect)

-- A few of basic definitions / lemmas

sn≤n→⊥ : ∀ {n : ℕ} → suc n ≤ n → ⊥
sn≤n→⊥ {suc n} (s≤s le) = sn≤n→⊥ le

≤-<⊎≡ : ∀ (m n : ℕ) → m ≤ n → (m < n) ⊎ (m ≡ n)
≤-<⊎≡ 0 zero z≤n = inj₂ refl
≤-<⊎≡ 0 (suc n) z≤n = inj₁ (s≤s z≤n)
≤-<⊎≡ (suc m) (suc n) (s≤s mn) with ≤-<⊎≡ m n mn
≤-<⊎≡ (suc m) (suc n) (s≤s mn) | inj₁ le = inj₁ (s≤s le)
≤-<⊎≡ (suc m) (suc n) (s≤s mn) | inj₂ eq = inj₂ (cong suc eq)

-- A few of basic definitions / lemmas

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

n≤ssn : ∀ (n : ℕ) → n ≤ suc (suc n)
n≤ssn zero = z≤n
n≤ssn (suc n) = s≤s (n≤ssn n)

sn≡m→n≤m : ∀ (n m : ℕ) → (suc n ≡ m) → n ≤ m
sn≡m→n≤m zero m eq = z≤n
sn≡m→n≤m (suc n) (suc (suc n)) refl = s≤s (n≤1+n n)

length : ∀ {X : Set} (xs : List X) → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

-- STLC definition

data Value : Set
data Type : Set

Id = ℕ
Env = List Value
TEnv = List Type

data Type where
  𝔹 : Type
  _↠_  : Type → Type → Type

data Term : Set where
  tt : Term
  ff : Term
  var : Id → Term
  app : Term → Term → Term
  lam : Term → Term

data Value where
  boolv : Bool → Value
  colv : Env → Term → Value

_⇓_ : ∀ {X : Set} (xs : List X) (n : ℕ) → Maybe X
[]       ⇓ n = nothing
(x ∷ xs) ⇓ n = if n ≡ᵇ (length xs) then just x else xs ⇓ n

data _⊢_∶_ : TEnv → Term → Type → Set where
  ty-tt : ∀ (Γ : TEnv) → Γ ⊢ tt ∶ 𝔹
  ty-ff : ∀ (Γ : TEnv) → Γ ⊢ ff ∶ 𝔹
  ty-var : ∀ (Γ : TEnv) (x : Id) (τ : Type)
    → Γ ⇓ x ≡ just τ
    → Γ ⊢ var x ∶ τ
  ty-app : ∀ (Γ : TEnv) (e1 e2 : Term) (τ1 τ2 : Type)
    → Γ ⊢ e1 ∶ (τ1 ↠ τ2)
    → Γ ⊢ e2 ∶ τ1
    → Γ ⊢ app e1 e2 ∶ τ2
  ty-abs : ∀ (Γ : TEnv) (e : Term) (τ1 τ2 : Type)
    --→ (τ1 ∷ (τ1 ↠ τ2) ∷ Γ) ⊢ e ∶ τ2 -- allows recursive function
    → (τ1 ∷ Γ) ⊢ e ∶ τ2
    → Γ ⊢ lam e ∶ (τ1 ↠ τ2)

data wf-env : Env → TEnv → Set
data _∶_ : Value → Type → Set

data wf-env where
  wf-nil  : wf-env [] []
  wf-cons : ∀ (v : Value) (τ : Type) (ρ : Env) (Γ : TEnv)
    → v ∶ τ
    → wf-env ρ Γ
    → wf-env (v ∷ ρ) (τ ∷ Γ)

data _∶_ where
  ty-bool-val : ∀ (v : Bool) → (boolv v) ∶ 𝔹
  ty-clo-val : ∀ (ρ : Env) (Γ : TEnv) (e : Term) (τ1 τ2 : Type)
    → wf-env ρ Γ
    --→ (τ1 ∷ (τ1 ↠ τ2) ∷ Γ) ⊢ e ∶ τ2
    → (τ1 ∷ Γ) ⊢ e ∶ τ2
    → (colv ρ e) ∶ (τ1 ↠ τ2)

eval : (n : ℕ) (ρ : Env) (e : Term) → Maybe (Maybe Value)
eval zero ρ e = nothing
eval (suc n) ρ tt = just (just (boolv true))
eval (suc n) ρ ff = just (just (boolv false))
eval (suc n) ρ (var x) = just (ρ ⇓ x)
eval (suc n) ρ (app e₁ e₂) with eval n ρ e₁
... | nothing = nothing
... | just nothing = just nothing
... | just (just (boolv x)) = just nothing
... | just (just (colv ρ′ body)) with eval n ρ e₂
...                                   | nothing = nothing
...                                   | just nothing = just nothing
...                                   | just (just v) = eval n (v ∷ ρ′) body
--...                                   | just (just v) = eval n (v ∷ (colv ρ′ body) ∷ ρ′) body
eval (suc n) ρ (lam e) = just (just (colv ρ e))

wf-length : ∀ (ρ : Env) (Γ : TEnv) → wf-env ρ Γ → length ρ ≡ length Γ
wf-length [] [] wf-nil = refl
wf-length (v ∷ ρ) (τ ∷ Γ) (wf-cons v τ ρ Γ x wf) = cong suc (wf-length ρ Γ wf)

index-max : ∀ {X : Set} (xs : List X) (n : ℕ) (x : X)
  → xs ⇓ n ≡ just x
  → n < length xs
index-max [] n x ()
index-max (x ∷ xs) n y eq with n ≡ᵇ (length xs) | ≡ᵇ⇒≡ n (length xs)
...                          | false            | _ with m≤n⇒m<n∨m≡n (index-max xs n y eq) -- ≤-<⊎≡ (suc n) (length xs) (index-max xs n y eq)
...                                                    | inj₁ rec-le = s≤s (≤-trans (n≤ssn n) rec-le)
...                                                    | inj₂ rec-eq = s≤s (sn≡m→n≤m n (length xs) rec-eq)
index-max (x ∷ xs) n x refl  | true             | p with p tt
...                                                    | refl = ≤-refl

index-extend : ∀ {X : Set} (xs : List X) (n : ℕ) (x y : X)
  → xs ⇓ n ≡ just x
  → (y ∷ xs) ⇓ n ≡ just x
index-extend xs n x y eq with n ≡ᵇ (length xs) | ≡ᵇ⇒≡ n (length xs)
...                         | false | _ = eq
...                         | true  | p with p tt
...                                        | refl with index-max xs (length xs) x eq
...                                                  | max = ⊥-elim (1+n≰n max)

index-safe-ex : ∀ (ρ : Env) (Γ : TEnv) (i : ℕ) (τ : Type)
  → wf-env ρ Γ
  → Γ ⇓ i ≡ just τ
  → Σ[ v ∈ Value ] (ρ ⇓ i ≡ just v) × (v ∶ τ)
index-safe-ex (v₁ ∷ ρ) (τ₁ ∷ Γ) i τ (wf-cons v₁ τ₁ ρ Γ v₁∶τ₁ wf) Γ⇓i rewrite wf-length ρ Γ wf
  with i ≡ᵇ length Γ | Γ⇓i
...  | false         | w = index-safe-ex ρ Γ i τ wf w
...  | true          | refl = ⟨ v₁ , ⟨ refl , v₁∶τ₁ ⟩ ⟩

full-safety : ∀ (n : ℕ) (e : Term) (τ : Type) (ρ : Env) (Γ : TEnv) (res : Maybe Value)
  → Γ ⊢ e ∶ τ
  → wf-env ρ Γ
  → eval n ρ e ≡ just res
  → Σ[ v ∈ Value ] (just v ≡ res) × (v ∶ τ)
full-safety (suc n) tt 𝔹 ρ Γ res wt wf refl = ⟨ boolv true , ⟨ refl , ty-bool-val true ⟩ ⟩
full-safety (suc n) ff 𝔹 ρ Γ res wt wf refl = ⟨ boolv false , ⟨ refl , ty-bool-val false ⟩ ⟩
full-safety (suc n) (var x) τ ρ Γ res (ty-var Γ x τ Γ⇓x) wf refl      with index-safe-ex ρ Γ x τ wf Γ⇓x
... | ⟨ v , ⟨ ρ⇓x , v∶τ ⟩ ⟩ = ⟨ v , ⟨  sym ρ⇓x , v∶τ ⟩ ⟩
full-safety (suc n) (lam e) τ ρ Γ res (ty-abs Γ e τ1 τ2 wt) wf refl =
  ⟨ (colv ρ e) , ⟨ refl , ty-clo-val ρ Γ e τ1 τ2 wf wt ⟩ ⟩
full-safety (suc n) (app e1 e2) τ ρ Γ res (ty-app Γ e1 e2 τ1 τ e1wt e2wt) wf ev
  with eval n ρ e1 | inspect (eval n ρ) e1
... | just nothing | Eq.[ eqv1 ] = 
  case full-safety n e1 (τ1 ↠ τ) ρ Γ nothing e1wt wf eqv1 of λ{ () }
... | just (just (boolv b)) | Eq.[ eqv1 ] =
  case full-safety n e1 (τ1 ↠ τ) ρ Γ (just (boolv b)) e1wt wf eqv1 of λ{ ⟨ (boolv b) , ⟨ refl , () ⟩ ⟩ }
... | just (just (colv ρ' bd)) | Eq.[ eqv1 ]
  with eval n ρ e2 | inspect (eval n ρ) e2 | ev
... | nothing | v2eq        | ()
... | just v2 | Eq.[ eqv2 ] | w
  with full-safety n e1 (τ1 ↠ τ) ρ Γ (just (colv ρ' bd)) e1wt wf eqv1
    |  full-safety n e2  τ1      ρ Γ  v2                   e2wt wf eqv2
... | ⟨ colv ρ' bd , ⟨ refl , clo-tp@(ty-clo-val ρ' Γ₁ bd τ1 τ wf' app-res-tp) ⟩ ⟩
    | ⟨ v2' , ⟨ refl , v2't ⟩ ⟩ =
      --let ρ* = v2' ∷ colv ρ' bd ∷ ρ'
          --Γ* = (τ1 ∷ (τ1 ↠ τ) ∷ Γ₁)
      let ρ* = v2' ∷ ρ'
          Γ* = (τ1 ∷ Γ₁)
          wf* = wf-cons v2' τ1 ρ' Γ₁ v2't wf'
          -- (wf-cons v2' τ1 (colv ρ' bd ∷ ρ') ((τ1 ↠ τ) ∷ Γ₁) v2't (wf-cons (colv ρ' bd) (τ1 ↠ τ) ρ' Γ₁ clo-tp wf'))
       in full-safety n bd τ ρ* Γ* res app-res-tp wf* w

max : ∀ (m n : ℕ) → ℕ
max zero zero = zero
max zero (suc n) = suc n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

{-
sn : ∀ (e : Term) (τ : Type) (ρ : Env) (Γ : TEnv)
  → Γ ⊢ e ∶ τ
  → wf-env ρ Γ
  → Σ[ n ∈ ℕ ] Σ[ v ∈ Value ] eval n ρ e ≡ just (just v)
sn tt τ ρ Γ wt wf = ⟨ 1 , ⟨ (boolv true) , refl ⟩ ⟩
sn ff τ ρ Γ wt wf = ⟨ 1 , ⟨ boolv false , refl ⟩ ⟩
sn (var x) τ ρ Γ (ty-var Γ .x .τ Γ⇓x) wf  with index-safe-ex ρ Γ x τ wf Γ⇓x
... | ⟨ v , ⟨ ρ⇓x , v∶τ ⟩ ⟩ = ⟨ 1 , ⟨ v , cong just ρ⇓x ⟩ ⟩
sn (app e1 e2) τ ρ Γ (ty-app .Γ .e1 .e2 τ1 .τ e1wt e2wt) wf
  with sn e1 (τ1 ↠ τ) ρ Γ e1wt wf
... | ⟨ n1 , ⟨ v1 , e1⇓v1 ⟩ ⟩
  with full-safety n1 e1 (τ1 ↠ τ) ρ Γ (just v1) e1wt wf e1⇓v1
... | ⟨ (colv ρ' body) , ⟨ refl , ty-clo-val ρ' Γ' .body .τ1 .τ wfρ'Γ' body∶τ ⟩ ⟩
  with sn e2 τ1 ρ Γ e2wt wf
... | ⟨ n2 , ⟨ v2 , e2⇓v2 ⟩ ⟩
  with full-safety n2 e2 τ1 ρ Γ (just v2) e2wt wf e2⇓v2
... | ⟨ v2 , ⟨ refl , v2wt ⟩ ⟩ = {!!} -- here we don't have the inductive hypothesis for body
sn (lam e) τ ρ Γ wt wf = {!!}
-}
