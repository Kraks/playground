-- Ch9, Associated type

{-# LANGUAGE MultiParamTypeClasses, TypeFamilies #-}

class (Num a, Num b) => GPlus a b where
  type SumType a b :: *
  plus :: a -> b -> SumType a b

instance GPlus Int Int where
  type SumType Int Int = Float
  plus a b = fromIntegral (a + b)

fthree = plus (1::Int) (2::Int)

class Collection ce where
  type Element ce :: *
  empty :: ce
  insert :: Element ce -> ce -> ce
  member :: Element ce -> ce -> Bool

instance Eq a => Collection [a] where
  type Element [a] = a
  empty = []
  insert x xs = x:xs
  member x xs = elem x xs
