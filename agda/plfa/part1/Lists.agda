module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)
open import plfa.part1.Connectives using (_⊎_)

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- Append

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

++-assoc : ∀ {A : Set} → (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- Length

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

length-++ : ∀ {A : Set} → (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

-- Exercise

reverse-++-distrib : ∀ {A : Set} → (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x ∷ xs) ys rewrite reverse-++-distrib xs ys = ++-assoc (reverse ys) (reverse xs) [ x ]

reverse-involutive : ∀ {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ] =
  cong (x ∷_) (reverse-involutive xs)

-- Faster reverse

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ [ x ] ++ ys
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses xs rewrite shunt-reverse xs [] = ++-identityʳ (reverse xs)

-- Map

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

-- Exercise

map-compose : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (lemma f g)
  where
    lemma : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    lemma f g [] = refl
    lemma f g (x ∷ xs) = cong ((g ∘ f) x ∷_) (lemma f g xs)

map-++-distribute : ∀ {A B : Set} → (f : A → B) → (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys = cong (f x ∷_) (map-++-distribute f xs ys)

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node l x r) = node (map-Tree f g l) (g x) (map-Tree f g r)

-- Fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

foldr-id : ∀ {A : Set} → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-id [] = refl
foldr-id (x ∷ xs) = cong (x ∷_) (foldr-id xs)

fold-append : ∀ {A : Set} → (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
fold-append [] ys = refl
fold-append (x ∷ xs) ys = cong (x ∷_) (fold-append xs ys)

-- Exercise

product : List ℕ → ℕ
product = foldr _*_ 1

fold-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (xs ys : List A) (e : B)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
fold-++ _⊗_ [] ys e = refl
fold-++ _⊗_ (x ∷ xs) ys e = cong (_⊗_ x) (fold-++ _⊗_ xs ys e)

map-is-foldr : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (lemma f)
  where
    lemma : ∀ {A B : Set} → (f : A → B) (xs : List A) → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    lemma f [] = refl
    lemma f (x ∷ xs) = cong (_∷_ (f x)) (lemma f xs)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node l x r) = g (fold-Tree f g l) x (fold-Tree f g r)

map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D)
  → map-Tree f g ≡ fold-Tree (λ x → leaf (f x)) (λ t1 x t2 → node t1 (g x) t2)
map-is-fold-Tree f g = extensionality (lemma f g)
  where
    lemma : ∀ {A B C D : Set} (f : A → C) (g : B → D) (t : Tree A B)
      → map-Tree f g t ≡ fold-Tree (λ x → leaf (f x)) (λ t1 x t2 → node t1 (g x) t2) t
    lemma f g (leaf x) = refl
    lemma f g (node l x r) rewrite lemma f g l | lemma f g r = refl

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

postulate
  +-id : ∀ (n : ℕ) → n + zero ≡ n
  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
  +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)

*-expand : ∀ (n : ℕ) → n * n ≡ n + (n ∸ 1) * n
*-expand zero = refl
*-expand (suc n) = refl

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-comm (n + sum (downFrom n)) 2 ⟩
    2 * (n + sum (downFrom n))
  ≡⟨⟩
    n + sum (downFrom n) + (n + sum (downFrom n) + zero)
  ≡⟨ cong (λ x → n + sum (downFrom n) + x) (+-id (n + sum (downFrom n))) ⟩
    n + sum (downFrom n) + (n + sum (downFrom n))
  ≡⟨ +-assoc n (sum (downFrom n)) (n + sum (downFrom n)) ⟩
    n + (sum (downFrom n) + (n + sum (downFrom n)))
  ≡⟨ cong (n +_) (+-swap (sum (downFrom n)) n (sum (downFrom n))) ⟩
    n + (n + (sum (downFrom n) + sum (downFrom n)))
  ≡⟨ cong (λ x → (n + (n + (sum (downFrom n) + x)))) (sym (+-id (sum (downFrom n)))) ⟩
    n + (n + (2 * sum (downFrom n)))
  ≡⟨ cong (λ x → (n + (n + x))) (*-comm 2 (sum (downFrom n))) ⟩
    n + (n + (sum (downFrom n) * 2))
  ≡⟨ cong (λ x → (n + (n + x))) (sum-downFrom n) ⟩
    n + (n + n * (n ∸ 1))
  ≡⟨ cong (λ x → (n + (n + x))) (*-comm n (n ∸ 1)) ⟩
    n + (n + (n ∸ 1) * n)
  ≡⟨ cong (n +_) (sym (*-expand n)) ⟩
    n + n * n
  ≡⟨⟩
    (suc n) * ((suc n) ∸ 1)
  ∎

-- Monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid {ℕ} _+_ 0
+-monoid = record
  { assoc = +-assoc
  ; identityˡ = +-identityˡ
  ; identityʳ = +-identityʳ
  }

*-monoid : IsMonoid {ℕ} _*_ 1
*-monoid = record
  { assoc = *-assoc
  ; identityˡ = *-identityˡ
  ; identityʳ = *-identityʳ
  }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid = record
  { assoc = ++-assoc
  ; identityˡ = ++-identityˡ
  ; identityʳ = ++-identityʳ
  }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ (foldr _⊗_ e xs) ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    x ⊗ foldr _⊗_ y xs
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ ((foldr _⊗_ e xs) ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e ⊗-monoid [] ys = sym (identityˡ ⊗-monoid (foldr _⊗_ e ys))
foldr-monoid-++ _⊗_ e ⊗-monoid (x ∷ xs) ys =
  begin
    (x ⊗ foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (_⊗_ x) (foldr-monoid-++ _⊗_ e ⊗-monoid xs ys)⟩
    (x ⊗ (foldr _⊗_ e xs ⊗ foldr _⊗_ e ys))
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) (foldr _⊗_ e ys)) ⟩
    ((x ⊗ foldr _⊗_ e xs) ⊗ foldr _⊗_ e ys)
  ∎

-- Exercise

foldl : ∀ {A B : Set} (_⊗_ : B → A → B) (e : B) (xs : List A) → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → y ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ y xs
foldl-monoid f e m [] y = identityʳ m y
foldl-monoid _⊗_ e m (x ∷ xs) y rewrite identityˡ m x
                                       | sym (foldl-monoid _⊗_ e m xs x)
                                       | sym (foldl-monoid _⊗_ e m xs (y ⊗ x))
                                       | assoc m y x (foldl _⊗_ e xs) = refl

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl f e m = extensionality (lemma f e m)
  where
    lemma : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
            → (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
    lemma f e m [] = refl
    lemma _⊗_ e m (x ∷ xs) rewrite lemma _⊗_ e m xs
                                  | identityˡ m x
                                  | foldl-monoid _⊗_ e m xs x = refl

-- All

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- Any

data Any {A : Set} (P : A → Set) : List A → Set where
  here : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

-- All and append

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys = record
  { to = to xs ys
  ; from = from xs ys
  }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pxsys = ⟨ [] , Pxsys ⟩
    to (x ∷ xs) ys (Px ∷ Pxsys) with to xs ys Pxsys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      (All P xs × All P ys) → All P (xs ++ ys)
    from [] ys PxsPys = Data.Product.proj₂ PxsPys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

-- Exercise

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys = record { to = to xs ys ; from = from xs ys }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys any = _⊎_.inj₂ any
    to (x ∷ xs) ys (here px) = _⊎_.inj₁ (here px)
    to (x ∷ xs) ys (there any) with to xs ys any
    ... | _⊎_.inj₁ Pxs = _⊎_.inj₁ (there Pxs)
    ... | _⊎_.inj₂ Pys = _⊎_.inj₂ Pys
    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from [] ys (_⊎_.inj₂ Pys) = Pys
    from (x ∷ xs) ys (_⊎_.inj₁ (here Px)) = here Px
    from (x ∷ xs) ys (_⊎_.inj₁ (there Pxs)) = there (from xs ys (_⊎_.inj₁ Pxs))
    from (x ∷ xs) ys (_⊎_.inj₂ Pys) = there (from xs ys (_⊎_.inj₂ Pys))

-- Exercise All-++-≃ (stretch) TODO

-- Exercise ¬Any⇔All¬ (recommended) TODO

-- Exercise ¬Any≃All¬ (stretch) TODO

-- Exercise All-∀ (practice) TODO

-- Exercise Any-∃ (practice) TODO

-- Decidability of All

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p = foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P = ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? d [] = yes []
All? d (x ∷ xs) with d x | All? d xs
All? d (x ∷ xs) | yes Px | yes Pxs = yes (Px ∷ Pxs)
All? d (x ∷ xs) | yes Px | no ¬Pxs = no λ{ (Px' ∷ Pxs) → ¬Pxs Pxs }
All? d (x ∷ xs) | no ¬Px | b = no λ{ (Px ∷ Pxs) → ¬Px Px }

-- Exercise Any? TODO

-- Exercise split TODO
