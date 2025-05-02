-- kind

{-# LANGUAGE GADTs, KindSignatures, TypeSynonymInstances, 
    FlexibleInstances, EmptyDataDecls, DataKinds #-}

data P a = P (a, a)

data AbsTree k a =
    Leaf a
  | Node (k (AbsTree k a))

type BTree' a = AbsTree P a

type RoseTree' a = AbsTree [] a

---

data T :: * -> * where
  NIL :: T a
  CONS :: a -> T a -> T a

data Tree :: (* -> *) -> * -> * where
  L :: a -> Tree k a
  N :: k (Tree k a) -> Tree k a

type RoseTree a = Tree [] a

instance Show a => Show (RoseTree a) where
  show (L a) = show a
  show (N tree) = show tree

t :: RoseTree Int
t = N [N [L 5, L 8, N [L 1, L 2]], N [L 3]]

---

data KEmpty = Empty | NonEmpty
data List :: * -> KEmpty -> * where
  Nil :: List a Empty
  Cons :: a -> List a b -> List a NonEmpty

safeHead :: List a NonEmpty -> a
safeHead (Cons x _) = x
