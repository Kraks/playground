-- Ch9, Multi-parameters typeclass

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

import GHC.Float

class GEq a b where
  equals :: a -> b -> Bool

data Nat = Zero | Succ Nat deriving Show

instance GEq Nat [a] where
  equals a b = eq a b
    where eq Zero [] = True
          eq (Succ n) (x:xs) = eq n xs
          eq _ _ = False

t = equals (Succ Zero) [()]
f = equals (Succ Zero) [(), ()]

-- Functional dependencies
class Fun a b | a -> b where
  fun :: a -> b

instance Fun Int Nat where
  fun a = Zero

z = fun (5::Int)

-- Generic plus
class (Num a, Num b, Num c) => GPlus a b c | a b -> c where
  plus :: a -> b -> c

instance GPlus Int Float Float where
  plus a b = fromIntegral a + b

instance GPlus Float Int Float where
  plus a b = plus b a

instance GPlus Float Float Float where
  plus a b = a + b

--instance GPlus Int Float Double where
--  plus a b = fromIntegral a + float2Double b

class Mult a b c | a b -> c where
  mult :: a -> b -> c

data Vector = Vector Int Int Int deriving (Eq, Show)

instance Mult Vector Vector Int where
  mult (Vector x1 y1 z1) (Vector x2 y2 z2) = x1*x2 + y1*y2 + z1*z2

instance Mult Int Vector Vector where
  mult i (Vector x y z) = Vector (i*x) (i*y) (i*z)

-------

class Collection e ce | ce -> e where
  empty :: ce
  insert :: e -> ce -> ce
  member :: e -> ce -> Bool

instance Eq a => Collection a [a] where
  empty = []
  insert x xs = x:xs
  member = elem

