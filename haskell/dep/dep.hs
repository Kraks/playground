{-# LANGUAGE
    DataKinds
  , TypeFamilies
  , TypeOperators
#-}

data Nat = Z | S Nat

infixl 6 :+

type family (n :: Nat) :+ (m :: Nat) :: Nat
type instance Z     :+ m = m
type instance (S n) :+ m = S (n :+ m)

