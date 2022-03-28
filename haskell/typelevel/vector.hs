{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}              -- promote values to type-level
{-# LANGUAGE TypeFamilies #-}           -- enables type-level functions
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Prelude hiding (tail, head, replicate, length, map)

data Nat = Z | S Nat

data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data SBool b where
  STrue  :: SBool True
  SFalse :: SBool False

data Tree a = Leaf a
            | Node (Tree a) (Tree a)

data STree a where
  SLeaf :: a -> STree (Leaf a)
  SNode :: STree a -> STree a -> STree (Node a a)

infixl 6 :+
infixl 7 :*

type family (n :: Nat) :+ (m :: Nat) :: Nat
type instance Z     :+ m = m
type instance (S n) :+ m = S (n :+ m)

type family (n :: Nat) :* (m :: Nat) :: Nat
type instance Z     :* m = Z
type instance (S n) :* m = m :+ n :* m

(%:+) :: SNat n -> SNat m -> SNat (n :+ m)
SZ   %:+ m = m
SS n %:+ m = SS (n %:+ m)

data Vector a m =
    (m ~ Z) => Nil                              -- type-level equality
  | forall n . (m ~ S n) => (:-) a (Vector a n) -- existential quantificaiton

infixr 5 :-

deriving instance Eq a => Eq (Vector a n)
deriving instance Show a => Show (Vector a n)

toList :: Vector a n -> [a]
toList Nil = []
toList (x :- xs) = x : toList xs

head :: Vector a (S n) -> a
head (x :- _) = x

tail :: Vector a (S n) -> Vector a n
tail (x :- xs) = xs

append :: Vector a n -> Vector a m -> Vector a (n :+ m)
append Nil       ys = ys
append (x :- xs) ys = x :- append xs ys

replicate :: SNat n -> a -> Vector a n
replicate SZ     _ = Nil
replicate (SS n) a = a :- replicate n a

sLength :: Vector a n -> SNat n
sLength Nil = SZ
sLength (x :- xs) = SS (sLength xs)

map :: (a -> b) -> Vector a n -> Vector b n
map _ Nil = Nil
map f (x :- xs) = f x :- map f xs

class SingRep n where
  sing :: SNat n

instance SingRep Z where
  sing = SZ

instance SingRep n => SingRep (S n) where
  sing = SS (sing :: SNat n)

data SingInstance (n :: Nat) where
  SingInstance :: SingRep n => SingInstance n

singInstance :: SNat n -> SingInstance n
singInstance SZ     = SingInstance
singInstance (SS n) = case singInstance n of
                        SingInstance -> SingInstance

replicate' :: forall a n . SingRep n => a -> Vector a n
replicate' = replicate (sing :: SNat n)

transpose :: SingRep n => Vector (Vector a n) m -> Vector (Vector a m) n
transpose Nil = replicate' Nil
transpose (Nil :- _) = Nil
transpose ((x :- xs) :- xss) =
  case singInstance (sLength xs) of
    SingInstance -> (x :- map head xss) :- transpose (xs :- map tail xss)

data Ordinal (n :: Nat) where
  OZ :: Ordinal (S n)
  OS :: Ordinal n -> Ordinal (S n)

sIndex :: Ordinal n -> Vector a n -> a
sIndex OZ     (x :- _) = x
sIndex (OS n) (_ :- xs) = sIndex n xs

-- fromList
-- map, uncons, init, last
-- zipWithSame

main :: IO ()
main = do
  print $ head (1 :- 2 :- Nil)
  print $ tail (1 :- 2 :- Nil)
  print $ append (1 :- 2 :- Nil) (3 :- Nil)
  print $ replicate (SS (SS (SS SZ))) 42
  print $ transpose ((1 :- 2 :- 3 :- Nil) :- (2 :- 3 :- 4 :- Nil) :- Nil)
  print $ sIndex (OS OZ) (0 :- 1 :- 2 :- 3 :- 4 :- 5 :- Nil)
  -- print $ sIndex (OS OZ) (0 :- Nil) -- type error
  -- print $ head Nil                  -- type error
