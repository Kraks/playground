{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE InstanceSigs #-}

import Prelude hiding (id)

-- Final interpreter

{-
class Expr' repr where
lit :: Int -> repr
neg :: repr -> repr
add :: repr -> repr -> repr

instance Expr' Int where
lit n = n
neg x = -x
add a b = a + b

expr :: (Expr' repr) => repr
expr = add (lit 1) (lit 2)

eval' :: Int -> Int
eval' x = x

result :: Int
result = eval' expr
-}

-- Finally Tagless

class Expr rep where
  lam :: (rep a -> rep b) -> rep (a -> b)
  app :: rep (a -> b) -> (rep a -> rep b)
  lit :: a -> rep a

newtype Interp a = R { reify :: a }

instance Expr Interp where
  lam :: (Interp a -> Interp b) -> Interp (a -> b)
  lam f = R $ reify . f . R
  --lam f = R $ (\a -> reify $ f $ R a)
  app f a = R $ reify f $ reify a
  lit = R

eval :: Interp a -> a
eval e = reify e

e1 :: Expr rep => rep Int
e1 = app (lam (\x -> x)) (lit 3)

ex1 :: Int
ex1 = eval e1
