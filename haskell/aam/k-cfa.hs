-- A Machine for k-CFA-like approximation
-- Section 3.3, Systematic abstraction of abstract machines

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
type Time = [Exp]
type Env = Var :-> Addr
type k :-> v = Data.Map.Map k v
type Store = Addr :-> P(Storable)
type Σ = (Exp, Env, Store, Kont, Time)

data Addr = KAddr (Exp, Time)
          | BAddr (Var, Time) deriving (Eq, Ord, Show)

data Storable = Clo (Lambda, Env) 
              | Cont Kont deriving (Eq,Ord)

data Lambda = Var :=> Exp deriving (Eq, Ord)

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp deriving (Eq, Ord)

data Kont = Done 
          | Arg(Exp, Env, Addr) 
          | App(Lambda, Env, Addr) deriving (Eq,Ord)

----

instance Show Lambda where 
  show (v :=> e) = "<λ" ++ v ++ "." ++ show e ++ ">"

instance Show Exp where
  show (Ref v) = v
  show (Lam lam) = show lam
  show (e1 :@ e2) = "<" ++ show e1 ++ " " ++ show e2 ++ ">"

instance Show Storable where 
  show (Clo(lam, env)) = "Clo<" ++ show lam ++ "," ++ show env ++ ">"
  show (Cont k) = show k

instance Show Kont where
  show Done = "Done"
  show (Arg(e, env, k)) = "Arg<" ++ show e ++ "," ++ show env ++ "," ++ show k ++ ">"
  show (App(lam, env, k)) = "App<" ++ show lam ++ "," ++ show env ++ "," ++ show k ++ ">"

-- make a tuple
(==>) :: a -> b -> (a, b)
(==>) x y = (x, y)

-- insert into a map
(//) :: Ord a => (a :-> b) -> [(a, b)] -> (a :-> b)
(//) m [(x, y)] = Data.Map.insert x y m

-- merge entries into a large map lattice
(///) :: (Ord k, Lattice v) => (k :-> v) -> [(k, v)] -> (k :-> v)
(///) m [(k, v)] = Data.Map.insertWith (⊔) k v m

allocBind :: (Var, Time) -> Addr
allocBind (v, t) = BAddr (v, t)

allocKont :: (Exp, Time) -> Addr
allocKont (e, t) = KAddr (e, t)

k :: Int
k = 0

tick :: Σ -> Time
tick (e, _, _, _, t) = take k (e:t)

step :: Σ -> [Σ]
-- Variable
step ς@(Ref x, ρ, σ, κ, t) = [ (Lam lam, ρ', σ, κ, t') 
                             | Clo(lam, ρ') <- Data.Set.toList $ σ !! (ρ!x) ]
  where t' = tick(ς)
-- Application
step ς@(f :@ e, ρ, σ, κ, t) = [(f, ρ, σ', κ', t')]
  where a' = allocKont(f :@ e, t')
        σ' = σ /// [a' ==> Data.Set.singleton(Cont κ)]
        κ' = Arg(e, ρ, a')
        t' = tick(ς)
-- Argument Evaluation Cont
step ς@(Lam lam, ρ, σ, Arg(e, ρ', a'), t) = [(e, ρ', σ, App(lam, ρ, a'), t')]
  where t' = tick(ς)
-- Application Cont
step ς@(Lam lam, ρ, σ, App(x :=> e, ρ', a), t) = 
  [(e, ρ' // [x ==> a'], σ /// [a' ==> Data.Set.singleton(Clo(lam, ρ))], κ, t') 
    | Cont κ <- Data.Set.toList $ σ !! a ]
    where a' = allocBind(x, t')
          t' = tick(ς)
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
inject (e) = (e, Data.Map.empty, Data.Map.empty, Done, [])

-- test

states = aval (Lam("x" :=> (Ref "x")) :@ Lam("y" :=> (Ref "y")))
