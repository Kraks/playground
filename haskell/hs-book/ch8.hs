-- Chapter 8
import Data.Either

-- *: nullary type constractor 

disjoint :: [a] -> [b] -> [Either a b]
disjoint as bs = map Left as ++ map Right bs

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x) = f x
either _ g (Right y) = g y

partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers = foldr (Main.either left right) ([], [])
                   where left a (l, r) = (a:l, r)
                         right a (l, r) = (l, a:r)

data Pair a b = Pair a b
pfst (Pair a b) = a
psnd (Pair a b) = b

-----------

data Nat = Zero
         | Succ Nat 
         deriving (Show, Eq)

nat2int Zero = 0
nat2int (Succ n) = 1 + nat2int n

int2nat 0 = Zero
int2nat n = Succ (int2nat (n-1))

add Zero n = n
add (Succ m) n = Succ (add m n)

-----------

data Shape = Circle Float
           | Rect Float Float
           deriving (Show, Eq)

area (Circle r) = pi * r^2
area (Rect a b) = a * b

data BoolExp = TRUE | FALSE
             | IF BoolExp BoolExp BoolExp

eval TRUE = True
eval FALSE = False
eval (IF con b1 b2) | eval con = eval b1
                    | otherwise = eval b2

data List a = Nil
            | Cons a (List a)
            deriving (Eq, Show)

-- (A, Either B C) ~= Either (A,B) (A,C)
f :: (a, Either b c) -> Either (a, b) (a, c)
f (a, Left b) = Left (a, b)
f (a, Right c) = Right (a, c)

g :: Either (a, b) (a, c) -> (a, Either b c)
g (Left (a, b)) = (a, Left b)
g (Right (a, c)) = (a, Right c)

-- `newtype` could only has one constrcutor,
-- and only one parameter

-- newtype (Num a, Eq b) => T a b = NewType (a -> b)
-- Illegal datatype context (use DatatypeContexts)

data BTree a = Leaf a | BNode a (BTree a) (BTree a)

data Tree a = Node a [Tree a]

data CTLTree = CTLLeaf | CTLNode CTLTree CTLTree
               deriving Show
trees 0 = [CTLLeaf]
trees n = [CTLNode lt rt | l <- [0..(n-1)], lt <- trees l, rt <- trees (n-1-l)]

-- TODO Hoffman, 24 point

-- Zipper
data Zipper a = Zipper [a] a [a] deriving Show

fromList :: [a] -> Zipper a
fromList (x:xs) = Zipper [] x xs
fromList _ = error "empty list"

next :: Zipper a -> Zipper a
next (Zipper ys y (x:xs)) = Zipper (y:ys) x xs
next z = z

prev :: Zipper a -> Zipper a
prev (Zipper (y:ys) x xs) = Zipper ys y (x:xs)
prev z = z

-- Zipper based on tree structure
data Accumulate a = Empty
                  | R (Accumulate a) a (BTree a)
                  | L (Accumulate a) a (BTree a)

type Zipper' a = (BTree a, Accumulate a)

right, left, up :: Zipper' a -> Zipper' a
right (Node n l r, a) = (r, R a n l)
right a = a

left (Node n l r, a) = (l, L a n r)
left a = a

up (t, R a n l) = (Node n l t, a)
up (t, L a n r) = (Node n t r, a)
up z@(t, Empty) = z

-- Zipper based on list structure
data Branch a = R' a (BTree a) | L' a (BTree a)
type Zipper'' a = (BTree a, [Branch a])

