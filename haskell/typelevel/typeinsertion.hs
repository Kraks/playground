-- https://kseo.github.io/posts/2017-01-30-type-level-insertion-sort.html

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.TypeLits

-- Term-level insertion sort

sort :: (Ord a) => [a] -> [a]
sort [] = []
sort (x:xs) = insert x (sort xs)

insert :: (Ord a) => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) = insert' (compare x y) x y ys
  where
    insert' :: (Ord a) => Ordering -> a -> a -> [a] -> [a]
    insert' LT x y ys = x : y : ys
    insert' _  x y ys = y : insert x ys

-- Type-level insertion sort

type family Sort xs where
  Sort '[] = '[]
  Sort (x ': xs) = Insert x (Sort xs)

type family Insert x xs where
  Insert x '[] = x ': '[]
  Insert x (y ': ys) = Insert' (CmpNat x y) x y ys

type family Insert' b x y ys where
  Insert' 'LT x y ys = x ': y ': ys
  Insert' _   x y ys = y ': Insert x ys

type L = [1,3,2,4,6,8,1]

-- :kind! Sort L
