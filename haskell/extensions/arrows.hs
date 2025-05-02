{-# LANGUAGE Arrows #-}

import Control.Monad (guard)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Arrow (returnA, Kleisli(Kleisli), runKleisli)

f :: Int -> (Int, Int)
f = \x ->
  let y = 2 * x
      z1 = y + 3
      z2 = y - 5
   in (z1, z2)

fM :: Int -> Identity (Int, Int)
fM = \x -> do
  y <- return (2 * x)
  z1 <- return (y + 3)
  z2 <- return (y - 5)
  return (z1, z2)

fA :: Int -> (Int, Int)
fA = proc x -> do
  y  <- (2 *) -< x
  z1 <- (+ 3) -< y
  z2 <- (subtract 5) -< y
  returnA -< (z1, z2)

--------------------------------

range :: Int -> [Int]
range r = [-r .. r]

cM :: Int -> [(Int, Int)]
cM = \r -> do
  x <- range 5
  y <- range 5
  guard (x * x + y *y <= r * r)
  return (x, y)

type K = Kleisli

k :: (a -> m b) -> Kleisli m a b
k = Kleisli

runK :: Kleisli m a b -> (a -> m b)
runK = runKleisli

-- | arrow actions must be statically known.

cA :: Kleisli [] Int (Int, Int)
cA = proc r -> do
  x <- k range -< 5
  y <- k range -< 5
  k guard -< (x * x + y * y <= r * r)
  returnA -< (x, y)
