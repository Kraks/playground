-- Ch9, Foldable
import Data.Monoid
import Data.Foldable

-- should implement either foldMap or foldr
{-
class Foldable t where
  foldMap :: Monoid m => (a -> m) -> t a -> m
  foldMap f = foldr (mappend . f) mempty
  
  foldr :: (a -> b -> b) -> b -> t a -> b
  foldr f z t = appEndo (foldMap (Endo . f) t) z
-}

-- some tests
anyTrue = foldMap (Any . (even)) [1, 2, 3, 4]
anyTrue' = foldr (\x acc -> even x || acc) False [1, 2, 3, 4]

data Tree a = Leaf a | Node (Tree a) a (Tree a)

instance Foldable Tree where
  foldMap f (Leaf x) = f x
  foldMap f (Node l n r) = foldMap f l `mappend` f n `mappend` foldMap f r

flatten = foldMap (: [])
ott = flatten (Node (Leaf 1) 2 (Leaf 3))

sumTree = foldMap Sum
six = sumTree (Node (Leaf 1) 2 (Leaf 3))


