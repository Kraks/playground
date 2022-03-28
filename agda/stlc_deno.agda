{-# OPTIONS --without-K --safe #-}

module STLC where

open import Data.Nat
open import Data.List
open import Data.List.Any
open import Data.List.Membership.Propositional

open import Data.Bool
open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

infixr 10 _⟶_

data Type : Set where
  bool : Type
  unit : Type
  _⟶_  : Type → Type → Type

Env = List Type

typeDenot : Type → Set
typeDenot bool    = Bool
typeDenot unit    = ⊤
typeDenot (s ⟶ t) = typeDenot s → typeDenot t

wfEnv : Env → Set
wfEnv [] = ⊤
wfEnv (x ∷ env) = typeDenot x × wfEnv env

module Regular where

  infixr 10 Λ⟶_
  infixl 9 _$$_
  infixr 8 LET_IN_

  data Term : Env → Type → Set where
    var     : ∀ {T env} → T ∈ env → Term env T
    true    : ∀ {env} → Term env bool
    false   : ∀ {env} → Term env bool
    *       : ∀ {env} → Term env unit
    Λ⟶_     : ∀ {S T env} → Term (S ∷ env) T → Term env (S ⟶ T)
    _$$_    : ∀ {S T env} → Term env (S ⟶ T) → Term env S → Term env T
    LET_IN_ : ∀ {S T env} → Term env S → Term (S ∷ env) T → Term env T

  termDenot : ∀ {env T} → wfEnv env → Term env T → typeDenot T
  termDenot {.(_ ∷ _)} {_}        (fst , _) (var (here refl)) = fst
  termDenot {.(_ ∷ _)} {T}        (_ , snd) (var (there x))   = termDenot snd (var x)
  termDenot {env}      {.bool}    wf        true              = true
  termDenot {env}      {.bool}    wf        false             = false
  termDenot {env}      {.unit}    wf        *                 = tt
  termDenot {env}      {.(_ ⟶ _)} wf        (Λ⟶ t)            = λ z → termDenot (z , wf) t
  termDenot {env}      {T}        wf        (x $$ y)          = termDenot wf x (termDenot wf y)
  termDenot {env}      {T}        wf        (LET x IN y)      = termDenot (termDenot wf x , wf) y
