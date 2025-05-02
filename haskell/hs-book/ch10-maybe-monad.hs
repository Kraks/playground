-- Ch10, Maybe Monad

{-# LANGUAGE FlexibleInstances #-}

import Prelude hiding (Maybe, Just, Nothing)

data Maybe a = Just a | Nothing deriving Show

instance Functor Maybe where
  fmap f Nothing = Nothing
  fmap f (Just x) = Just (f x)

instance Applicative Maybe where
  pure = Just
  Nothing <*> _ = Nothing
  (Just f) <*> arg = fmap f arg

instance Monad Maybe where
  return = Just
  (Just a) >>= f = f a
  Nothing >> _ = Nothing
  fail _ = Nothing

just3 :: Maybe Int
just3 = return 3

list3 :: [] Int
list3 = return 3

-----

data Exp = Lit Integer
         | Add Exp Exp
         | Sub Exp Exp
         | Mul Exp Exp
         | Div Exp Exp

safeEval :: Exp -> Maybe Integer
safeEval (Lit n) = return n
safeEval (Add e1 e2) = safeEval e1 >>= \n1 -> 
                       safeEval e2 >>= \n2 ->
                       return (n1+n2)
safeEval (Sub e1 e2) = safeEval e1 >>= \n1 -> 
                       safeEval e2 >>= \n2 ->
                       return (n1-n2)
safeEval (Mul e1 e2) = safeEval e1 >>= \n1 -> 
                       safeEval e2 >>= \n2 ->
                       return (n1*n2)
safeEval (Div e1 e2) = safeEval e1 >>= \n1 -> 
                       safeEval e2 >>= \n2 ->
                         if n2 == 0 then Nothing
                                    else return (n1 `div` n2)

-- MonadPlus

class Monad m => MonadPlus m where
  mzero :: m a
  mplus :: m a -> m a -> m a

instance MonadPlus m => Monoid (m a) where
  mempty = mzero
  mappend = mplus

instance MonadPlus [] where
  mzero = []
  mplus = (++)

instance MonadPlus Maybe where
  mzero = Nothing
  Nothing `mplus` ys = ys
  xs `mplus` ys = xs
