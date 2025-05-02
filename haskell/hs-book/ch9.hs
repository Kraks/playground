-- Chapter 9

{-# LANGUAGE MultiParamTypeClasses, InstanceSigs, GADTs #-}

import Prelude hiding (Functor, fmap, Applicative, (<*>), (<$>),
                       pure, (<|>), Alternative)

data MyNum = One | Two | Three

instance Show MyNum where
  show One = "1"
  show Two = "2"
  show Three = "3"

class Functor f where
  fmap :: (a -> b) -> f a -> f b

(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) = fmap

newtype Container a = Container a 

instance Functor Container where
  fmap f (Container a) = Container (f a)

instance Functor [] where
  fmap = map

instance Functor Maybe where
  fmap f Nothing = Nothing
  fmap f (Just x) = Just (f x)

instance Functor ((->) r) where
  fmap f g = (\x -> f (g x))
  -- fmap f g = (.)

data Tree a = Leaf a | Branch (Tree a) (Tree a) 
              deriving Show

instance Functor Tree where
  fmap f (Leaf x) = Leaf (f x)
  fmap f (Branch l r) = Branch (fmap f l) (fmap f r)

data Tree' a = Leaf' a | Branch' (Tree' (a, a))
              deriving Show

-- TODO fmap for Tree'

-- Applicative
-- f here is a type, or say container
class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

instance Applicative Maybe where
  pure = Just
  Nothing <*> _ = Nothing
  (Just f) <*> arg = fmap f arg

three = Just (+) <*> Just 1 <*> Just 2
nine = (+) <$> Just 5 <*> Just 4 -- (fmap (+) (Just 4)) <*> (Just 5)
ten = pure (+) <*> Just 5 <*> Just 5 -- liftA2 (+) (Just 5) (Just 5)


liftA :: Applicative f => (a -> b) -> f a -> f b
liftA f a = pure f <*> a

liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f a b = f <$> a <*> b

infixl 4 <*>, <*, *>
(*>) :: Applicative f => f a -> f b -> f b
u *> v = pure (const id) <*> u <*> v
-- (*>) = liftA2 (const id)

(<*) :: Applicative f => f a -> f b -> f a
u <* v = pure const <*> u <*> v
-- (<*) = listA2 const

-- List as Applicative
instance Applicative [] where
  pure x = [x]
  fs <*> xs = [f x | f <- fs, x <- xs]

lstAdd1 = (\x -> x+1) <$> [1, 2, 3]
lstAdd1' = fmap (\x -> x+1) [1, 2, 3]
lstAdd1'' = [\x -> x+1] <*> [1, 2, 3]

addLists :: Num a => [a] -> [a] -> [a]
--addLists xs ys = (+) <$> xs <*> ys
addLists xs ys = [(+)] <*> xs <*> ys

instance Applicative ((->) r) where
  pure :: a -> r -> a
  pure x y = x
  (<*>) :: (r -> a -> b) -> (r -> a) -> r -> b
  (<*>) f g x = f x (g x)

-- identity
just5 = pure id <*> Just 5

-- composition
justTrue = (Just not) <*> ((Just even) <*> (Just 5))
justTrue' = pure (.) <*> (Just not) <*> (Just even) <*> (Just 5)

-- homomorphism
justSix = Just (+1) <*> Just 5
justSix' = Just (6+1)

-- interchange
justSix'' = pure ($ 5) <*> Just (+1) -- pure ($ y) = pure (\f -> f $ y)

-- Alternative
infix 3 <|>

class Applicative f => Alternative f where
  empty :: f a
  (<|>) :: f a -> f a -> f a

instance Alternative Maybe where
  empty = Nothing
  Nothing <|> p = p
  Just x <|> _ = Just x

instance Alternative [] where
  empty = []
  (<|>) = (++)

some :: Alternative f => f a -> f [a]
some v = some_v
  where many_v = some_v <|> pure []
        some_v = (:) <$> v <*> many_v

many :: Alternative f => f a -> f [a]
many v = many_v
  where many_v = some_v <|> pure []
        some_v = (:) <$> v <*> many_v

-- 9.6
data Rect = Rect Double Double deriving Show
data Circle = Circle Double deriving Show

class HasArea t where area :: t -> Double

instance HasArea Rect where
  area (Rect a b) = a * b

instance HasArea Circle where
  area (Circle r ) = pi * r * r

data Shape where
  Shape :: (Show t, HasArea t) => t -> Shape

instance Show Shape where
  show (Shape shape) = "Shape " ++ (show shape)

instance HasArea Shape where
  area (Shape shape) = area shape

shapes = [Shape (Rect 2 3), Shape (Circle 1.0)]
areas = map area shapes

