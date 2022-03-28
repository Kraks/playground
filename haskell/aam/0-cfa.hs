-- A Machine for 0-CFA-like approximation
-- Section 3.4, Systematic abstraction of abstract machines

{-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

import Data.Map
import Data.Set
import Prelude hiding ((!!))

-- Lattice
class Lattice a where
  bot :: a
  top :: a
  (⊑) :: a -> a -> Bool
  (⊔) :: a -> a -> a    -- any two elements both have a least upper bound
  (⊓) :: a -> a -> a    -- any two elements both have a greatest lower bound

type P s = Data.Set.Set s

instance (Ord s, Eq s) => Lattice (P s) where
  bot = Data.Set.empty
  top = error "no representation of universal set"
  x ⊑ y = x `Data.Set.isSubsetOf` y
  x ⊔ y = x `Data.Set.union` y
  x ⊓ y = x `Data.Set.intersection` y

instance (Ord k, Lattice v) => Lattice (k :-> v) where
  bot = Data.Map.empty
  top = error "no representation of universal set"
  f ⊑ g = Data.Map.isSubmapOfBy (⊑) f g
  f ⊔ g = Data.Map.unionWith (⊔) f g
  f ⊓ g = Data.Map.intersectionWith (⊓) f g 

(!!) :: (Ord k, Lattice v) => (k :-> v) -> k -> v
f !! k = Data.Map.findWithDefault bot k f

----

type Var = String
type k :-> v = Data.Map.Map k v
type Store = Addr :-> P(Storable)
type Σ = (Exp, Store, Kont)

data Addr = KAddr Exp
          | BAddr Var deriving (Eq, Ord, Show)

data Storable = Clo Lambda
              | Cont Kont deriving (Eq,Ord)

data Lambda = Var :=> Exp deriving (Eq, Ord)

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp deriving (Eq, Ord)

data Kont = Done 
          | Arg(Exp, Addr) 
          | App(Lambda, Addr) deriving (Eq,Ord)

----

instance Show Lambda where 
  show (v :=> e) = "<λ" ++ v ++ "." ++ show e ++ ">"

instance Show Exp where
  show (Ref v) = v
  show (Lam lam) = show lam
  show (e1 :@ e2) = "<" ++ show e1 ++ " " ++ show e2 ++ ">"

instance Show Storable where 
  show (Clo(lam)) = "Clo<" ++ show lam ++ ">"
  show (Cont k) = show k

instance Show Kont where
  show Done = "Done"
  show (Arg(e, k)) = "Arg<" ++ show e ++ "," ++ show k ++ ">"
  show (App(lam, k)) = "App<" ++ show lam ++ "," ++ show k ++ ">"

-- make a tuple
(==>) :: a -> b -> (a, b)
(==>) x y = (x, y)

-- insert into a map
(//) :: Ord a => (a :-> b) -> [(a, b)] -> (a :-> b)
(//) m [(x, y)] = Data.Map.insert x y m

-- merge entries into a large map lattice
(///) :: (Ord k, Lattice v) => (k :-> v) -> [(k, v)] -> (k :-> v)
(///) m [(k, v)] = Data.Map.insertWith (⊔) k v m

step :: Σ -> [Σ]
-- Variable
step (Ref x, σ, κ) = [ (Lam lam, σ, κ) | Clo(lam) <- Data.Set.toList $ σ !! (BAddr x) ]

-- Application
step (f :@ e, σ, κ) = [(f, σ', κ')]
  where a' = KAddr(f :@ e)
        σ' = σ /// [a' ==> Data.Set.singleton(Cont κ)]
        κ' = Arg(e, a')

-- Argument Evaluation Cont
step (Lam lam, σ, Arg(e, a')) = [(e, σ, App(lam, a'))]

-- Application Cont
step (Lam lam, σ, App(x :=> e, a)) =
  [ (e, σ /// [BAddr x ==> Data.Set.singleton(Clo(lam))], κ)
  | Cont κ <- Data.Set.toList $ σ !! a ]

step s = [s]

aval :: Exp -> P(Σ)
aval (e) = explore step (inject(e))

explore :: (Ord a) => (a -> [a]) -> a -> P(a)
explore f ς0 = search f Data.Set.empty [ς0]

(∈) :: Ord a => a -> P(a) -> Bool
(∈) = Data.Set.member

search :: (Ord a) => (a -> [a]) -> P(a) -> [a] -> P(a)
search f seen [] = seen
search f seen (hd:tl)
  | hd ∈ seen = search f seen tl
  | otherwise = search f (Data.Set.insert hd seen) (f(hd) ++ tl)

inject :: Exp -> Σ
inject (e) = (e, Data.Map.empty, Done)

-- test

states = aval (Lam("x" :=> (Ref "x")) :@ Lam("y" :=> (Ref "y")))
