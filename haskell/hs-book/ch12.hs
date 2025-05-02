-- Chapter 12

{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies #-}

import Data.Monoid

-- Writer Monad
newtype Writer w a = Writer { runWriter :: (a, w) } deriving Show
writer = Writer

instance Functor (Writer w) where
  fmap f (Writer (x, v)) = Writer (f x, v)

instance (Monoid w) => Applicative (Writer w) where
  pure x = Writer (x, mempty)
  (Writer (f, z)) <*> (Writer (x, y)) = Writer (f x, y)

instance (Monoid w) => Monad (Writer w) where
  return x = Writer (x, mempty)
  Writer (x,v) >>= f = let (Writer (y, v')) = f x
                        in Writer (y, v `mappend` v')

left', right' :: Int -> Writer String Int
left' x = writer (x-1, "move left\n")
right' x = writer (x+1, "move right\n")

move' i = do x <- left' i
             y <- left' x
             return y

move'' i = left' i >>= \x ->
           left' x >>= \y ->
           return y

two = runWriter $ move' 4
two' = runWriter $ move'' 4

