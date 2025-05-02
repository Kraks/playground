-- Time-stamped CESK* Machine
-- Section 2.8, Systematic abstraction of abstract machines

{-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

import Prelude
import Data.Map

type Σ = (Exp, Env, Store, Kont, Time)

type Var = String
type Addr = Int
type Time = Int

data Lambda = Var :=> Exp

instance Show Lambda where 
  show (v :=> e) = "<λ" ++ v ++ "." ++ show e ++ ">"

----

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp

instance Show Exp where
  show (Ref v) = v
  show (Lam lam) = show lam
  show (e1 :@ e2) = "<" ++ show e1 ++ " " ++ show e2 ++ ">"

----

type k :-> v = Data.Map.Map k v

type Env = Var :-> Addr

----

type Store = Addr :-> Storable

data Storable = Clo(Lambda, Env)
              | Cont Kont

instance Show Storable where 
  show (Clo(lam, env)) = "Clo<" ++ show lam ++ "," ++ show env ++ ">"
  show (Cont k) = show k

----

data Kont = Done | Arg(Exp, Env, Addr) | App(Lambda, Env, Addr)

instance Show Kont where
  show Done = "Done"
  show (Arg(e, env, k)) = "Arg<" ++ show e ++ "," ++ show env ++ "," ++ show k ++ ">"
  show (App(lam, env, k)) = "App<" ++ show lam ++ "," ++ show env ++ "," ++ show k ++ ">"

----

-- make a tuple
(==>) :: a -> b -> (a, b)
(==>) x y = (x, y)

-- insert into a map
(//) :: Ord a => (a :-> b) -> [(a, b)] -> (a :-> b)
(//) m [(x, y)] = Data.Map.insert x y m

alloc :: Σ -> Addr
alloc (_, _, s, _, _) = (Prelude.foldl max 0 $ keys s) + 1

tick :: Σ -> Time
tick (_, _, _, _, t) = t + 1

step :: Σ -> Σ
-- Variable
step ς@(Ref x, ρ, σ, κ, t) = (Lam lam, ρ', σ, κ, t') 
  where Clo(lam, ρ') = σ!(ρ!x)
        t' = tick(ς)
-- Application
step ς@(f :@ e, ρ, σ, κ, t) = (f, ρ, σ', κ', t')
  where a' = alloc(ς)
        σ' = σ // [a' ==> Cont κ]
        κ' = Arg(e, ρ, a')
        t' = tick(ς)
-- Argument Evaluation Cont
step ς@(Lam lam, ρ, σ, Arg(e, ρ', a'), t) = (e, ρ', σ, App(lam, ρ, a'), t')
  where t' = tick(ς)
-- Application Cont
step ς@(Lam lam, ρ, σ, App(x :=> e, ρ', a), t) = 
  (e, ρ' // [x ==> a'], σ // [a' ==> Clo(lam, ρ)], κ, t') 
  where a' = alloc(ς)
        Cont κ = σ ! a
        t' = tick(ς)

inject :: Exp -> Σ
inject (e) = (e, Data.Map.empty, Data.Map.empty, Done, 0)

collect :: (a -> a) -> (a -> Bool) -> a -> [a]
collect f isFinal ς0 | isFinal ς0 = [ς0]
                     | otherwise = ς0 : (collect f isFinal (f(ς0)))

isFinal :: Σ -> Bool
isFinal (Lam _, _, _, Done, _) = True
isFinal _ = False

evaluate :: Exp -> [Σ]
evaluate e = collect step isFinal (inject(e))

states = evaluate (Lam("x" :=> (Ref "x")) :@ Lam("y" :=> (Ref "y")))
