-- Code from Dependently Typed Programming in Agda

module DTPin where

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

_+_ : Nat → Nat → Nat
zero   + m = m
succ n + m = succ (n + m)

_*_ : Nat → Nat → Nat
zero   * m = zero
succ n * m = m + n * m

_or_ : Bool → Bool → Bool
false or x = x
true  or x = true

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix  5  if_then_else_

infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

identity : (A : Set) → A → A
identity A x = x

zero' : Nat
zero' = identity Nat zero

apply : (A : Set) (B : A → Set) →
        ((x : A) → B x) → (a : A) → B a
apply A B f a = f a

identity₂ : (A : Set) → A → A
identity₂ = \A x -> x

identity₃ : (A : Set) → A → A
identity₃ = \(A : Set)(x : A) → x

id : {A : Set} → A → A
id x = x

true' : Bool
true' = id true

silly : {A : Set}{x : A} → A
silly {_}{x} = x

false' : Bool
false' = silly {x = Bool.false}

one : Nat
one = identity _ (succ zero)

identity_im : {A : Set} → A → A
identity_im {A} x = x

one' : Nat
one' = identity_im (succ zero)

_∘_ : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
      (f : {x : A} (y : B x) → C x y) (g : (x : A) → B x)
      (x : A) → C x (g x)
(f ∘ g) x = f (g x)

plus-two = succ ∘ succ

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- 2.4 Datatype Families

data Vec (A : Set) : Nat → Set where
  []   : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

head : {A : Set} {n : Nat} → Vec A (succ n) → A
head (x :: xs) = x

tail : {A : Set} {n : Nat} → Vec A (succ n) → Vec A n
tail (x :: xs) = xs

-- Dot Patterns

vmap : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data Vec₂ (A : Set) : Nat → Set where
  nil  : Vec₂ A zero
  cons : (n : Nat) → A → Vec₂ A n → Vec₂ A (succ n)

vmap₂ : {A B : Set} (n : Nat) → (A → B) → Vec₂ A n → Vec₂ B n
vmap₂ .zero     f nil           = nil
vmap₂ .(succ n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)

vmap₃ : {A B : Set} (n : Nat) → (A → B) → Vec₂ A n → Vec₂ B n
vmap₃ zero      f nil            = nil
vmap₃ (succ n)  f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)

data Image_∋_ {A B : Set} (f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

inv : {A B : Set} (f : A → B) (y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

-- Absurd Patterns

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (succ n)
  fsucc : {n : Nat} → Fin n → Fin (succ n)

magic : {A : Set} → Fin zero → A
magic ()

data Empty : Set where
  empty : Fin zero → Empty

magic' : {A : Set} → Empty → A
magic' (empty ())

_!_ : {n : Nat}{A : Set} → Vec A n → Fin n → A
[]        ! ()
(x :: xs) ! fzero     = x
(x :: xs) ! (fsucc i) = xs ! i

-- Construct a list given a function from indices to elements.
tabulate : {n : Nat} {A : Set} → (Fin n → A) → Vec A n
tabulate {zero}   f = []
tabulate {succ n} f = f fzero :: tabulate (f ∘ fsucc)

-- 2.5 Programs as Proofs

data   False : Set where
record True  : Set where --no fields.

trivial : True
trivial = record{}

trivial' : True
trivial' = _

isTrue : Bool → Set
isTrue true = True
isTrue false = False

_<_ : Nat → Nat → Bool
_      < zero = false
zero   < succ n = true
succ m < succ n = m < n

length : {A : Set} → List A → Nat
length []        = zero
length (x :: xs) = succ (length xs)

lookup : {A : Set} (xs : List A) (n : Nat) →
         isTrue (n < length xs) → A
lookup []        n        ()
lookup (x :: xs) zero     p = x
lookup (x :: xs) (succ n) p = lookup xs n p

result = lookup ((succ zero) :: (succ (succ zero)) :: []) zero trivial
result' = lookup ((succ zero) :: (succ (succ zero)) :: []) (succ zero) trivial

-- Use datatype families to define propositions.
-- For a type A and an element x of A, define the family of proofs of
-- "being equal to x".
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

_⇆_ : {A : Set} {a b c : A} → a == b → b == c → a == c
_⇆_ refl refl = refl

_⇆₁_ : {A : Set} {a b c : A} → a == b → b == c → a == c
_⇆₁_ ab bc with ab   | bc
...            | refl | refl = refl

⋙ : ∀ {A : Set} {B : Set} {m n} {f : A → B} → m == n → (f m) == (f n)
⋙ refl = refl

trivialEq : ∀ {A : Set} {a : A} → a == a
trivialEq = refl

data _≤_ : Nat → Nat → Set where
  leq-zero : {n : Nat} → zero ≤ n
  leq-succ : {m n : Nat} → m ≤ n → succ m ≤ succ n

leq-trans : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-succ p) (leq-succ q) = leq-succ (leq-trans p q)

-- 2.6 More on pattern matching

min : Nat → Nat → Nat
min x y with x < y
min x y | true  = x
min x y | false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

data _≠_ : Nat → Nat → Set where
  z≠s : {n : Nat} → zero ≠ succ n
  s≠z : {n : Nat} → succ n ≠ zero
  s≠s : {m n : Nat} → m ≠ n → succ m ≠ succ n

data Equal? (n m : Nat) : Set where
  eq  : n == m → Equal? n m
  neq : n ≠  m → Equal? n m

equal? : (n m : Nat) → Equal? n m
equal? zero zero = eq refl
equal? zero (succ m) = neq z≠s
equal? (succ n) zero = neq s≠z
equal? (succ n) (succ m) with equal? n m
... | eq refl = eq refl
... | neq p = neq (s≠s p)

infix 20 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} → xs ⊆ ys → xs ⊆ y :: ys
  keep : forall {x xs ys} → xs ⊆ ys → x :: xs ⊆ x :: ys

-- Prove that filter computes a sublist of its argument
lem-filter : {A : Set} (p : A → Bool) (xs : List A) →
             filter p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x :: xs) with p x
... | true  = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)

lem-plus-zero : (n : Nat) → n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (succ m) with m + zero | lem-plus-zero m
... | .m | refl = refl

-- 2.7 Modules

module M where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A → Maybe A

  maybe : {A B : Set} → B → (A → B) → Maybe A → B
  maybe z f nothing = z
  maybe z f (just x) = f x

module A where
  private
    internal : Nat
    internal = zero
  exported : Nat → Nat
  exported n = n + internal

mapMaybe₁ : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
mapMaybe₁ f M.nothing = M.nothing
mapMaybe₁ f (M.just x) = M.just (f x)

mapMaybe₂ : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
mapMaybe₂ f m = let open M in
  maybe nothing (just ∘ f) m

open M

open M hiding (maybe)
  renaming (Maybe to _option;
            nothing to none;
            just to some)

mapOption : {A B : Set} → (A → B) → A option → B option
mapOption f none = none
mapOption f (some x) = some (f x)

mtrue : Maybe Bool
mtrue = mapOption not (just false)

-- Parameterised modules

module Sort (A : Set) (_<_ : A → A → Bool) where
  insert : A → List A → List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true  = x :: insert y xs
  ... | false = y :: x :: xs

  sort : List A → List A
  sort [] = []
  sort (x :: xs) = insert x (sort xs)

module SortNat = Sort Nat _<_

sort₁ : List Nat → List Nat
sort₁ = SortNat.sort

open Sort Nat _<_ renaming (insert to insertNat; sort to sortNat)

module Lists (A : Set) (_<_ : A → A → Bool) where
  open Sort A _<_ public

  minimum : List A → Maybe A
  minimum xs with sort xs
  ... | [] = nothing
  ... | y :: ys = just y

-- 2.8 Records

record Point : Set where
  field x : Nat
        y : Nat

mkPoint : Nat → Nat → Point
mkPoint a b = record { x = a; y = b }

getX : Point → Nat
getX = Point.x

abs : Point → Nat
abs p = let open Point p in x * x + y * y

record Monad (M : Set → Set) : Set1 where
  field
    return : {A : Set} → A → M A
    _>>=_ : {A B : Set} → M A → (A → M B) → M B

  mapM : {A B : Set} → (A → M B) → List A → M (List B)
  mapM f [] = return []
  mapM f (x :: xs) = f x       >>= \y  →
                     mapM f xs >>= \ys →
                     return (y :: ys)

mapM' : {M : Set → Set} → Monad M →
        {A B : Set} → (A → M B) → List A → M (List B)
mapM' Mon f xs = Monad.mapM Mon f xs

-- Exercise 2.1
-- Matrix transposition

Matrix : Set → Nat → Nat → Set
Matrix A n m = Vec (Vec A n) m

-- (a)
vec : {n : Nat} {A : Set} → A → Vec A n
vec {zero} x = []
vec {succ n} x = x :: vec {n} x

-- (b)
infixl 90 _$_
_$_ : {n : Nat}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
[] $ [] = []
(f :: fs) $ (x :: xs) = f x :: fs $ xs

-- (c)
transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
transpose {_} {zero} {_} xss = []
transpose {_} {succ n} {m} xss = (vmap head xss) :: transpose (vmap tail xss)

-- Exercise 2.2
-- Vector loopup

lem-!-tab : ∀ {A n} (f : Fin n → A) (i : Fin n) →
            (tabulate f ! i) == f i
lem-!-tab f fzero = refl
lem-!-tab f (fsucc i) = lem-!-tab (f ∘ fsucc) i

lem-tab-! : ∀ {A n} (xs : Vec A n) → tabulate (_!_ xs) == xs
lem-tab-! [] = refl
lem-tab-! (x :: xs) with tabulate (_!_ xs) | lem-tab-! xs
lem-tab-! (x :: xs) | .xs | refl = refl

-- Exercise 2.3

-- (a) Prove the reflexivity and transitivity of ⊆

⊆-refl : {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl {xs = []} = stop
⊆-refl {xs = x :: ys} = keep ⊆-refl

⊆-trans : {A : Set} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans stop q = q
⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
⊆-trans p        (drop q) = drop (⊆-trans p q)
-- ⊆-trans (keep p) (drop q) = drop (⊆-trans (keep p) q)
-- ⊆-trans (drop p) (drop q) = drop (⊆-trans (drop p) q)

-- infixr 30 _::_
data SubList {A : Set} : List A → Set where
  [] : SubList []
  _::_ : ∀ x {xs} → SubList xs → SubList (x :: xs)
  skip : ∀ {x xs} → SubList xs → SubList (x :: xs)

-- (b) Define a function to extract the list corresponding to a sublist

forget : {A : Set} {xs : List A} → SubList xs → List A
forget [] = []
forget (x :: s) = x :: forget s
forget (skip s) = forget s

-- (c) Now, prove that a SubList is a sublist in the sense of ⊆

lem-forget : {A : Set} {xs : List A} (zs : SubList xs) → forget zs ⊆ xs
lem-forget zs = {!!}
