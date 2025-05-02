{-# LANGUAGE FlexibleInstances #-}
module Paper where

import Prelude hiding (Monad, Maybe, Just, Nothing, (>>=), return)

class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- Section 2.1 Maybe Monad

data Maybe a = Just a | Nothing

instance Monad Maybe where
  return a = Just a
  x >>= f = case x of
    Just a -> f a
    Nothing -> Nothing

-- Section 2.2 State Monad

newtype StateMonad s a = SM (s -> (a, s))

instance Monad (StateMonad s) where
  return a = SM (\s -> (a, s))
  x >>= f = SM (\s -> let SM g = x
                          (a, s') = g s
                          SM f' = f a
                     in f' s')

fetch :: StateMonad s s
fetch = SM (\s -> (s, s))

set :: s -> StateMonad s ()
set x = SM (\_ -> ((), x))

tick :: StateMonad Int Int
tick = fetch >>= \n ->
  set (n + 1) >>= \_ ->
  return n

-- Section 2.3 Monadic parsing

newtype Parser s a = P ([s] -> Maybe (a, [s]))

symbol :: Eq s => s -> Parser s s
symbol s = P (\xs -> case xs of
                 [] -> Nothing
                 (x : xs') -> if x == s then Just (s, xs') else Nothing)

-- Section 2.4

liftM2 :: Monad m => (a -> b -> c) -> m a -> m b -> m c
liftM2 op x y = x >>= \a -> y >>= \b -> return (a `op` b)

-- Section 2.5

class Monad m => MonadZero m where
  zero :: m a

class MonadZero m => MonadPlus m where
  (++) :: m a -> m a -> m a

-- Section 4

class Arrow a where
  arr :: (b -> c) -> a b c
  (>>>) :: a b c -> a c d -> a b d

newtype Kleisli m a b = K (a -> m b)

instance Monad m => Arrow (Kleisli m) where
  arr f = K (\b -> return (f b))
  K f >>> K g = K (\b -> f b >>= g)
