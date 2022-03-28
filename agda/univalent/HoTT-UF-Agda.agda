{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-Agda where

open import Universes public

variable 𝓤 𝓥 𝓦 𝓣 : Universe

data One : 𝓤₀ ̇ where
  ⋆ : One
