-- Store-allocated CESK* Machine
-- Section 2.6, Systematic abstraction of abstract machines

{-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

import Prelude
import Data.Map

type Σ = (Exp, Env, Store, Kont)

type Addr = Int
type Var = String
type k :-> v = Data.Map.Map k v
type Env = Var :-> Addr
type Store = Addr :-> Storable

data Lambda = Var :=> Exp

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp

data Kont = Done 
          | Arg(Exp, Env, Addr) 
          | App(Lambda, Env, Addr)

data Storable = Clo(Lambda, Env)
              | Cont Kont

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

alloc :: Store -> Addr
alloc(s) = (Prelude.foldl max 0 $ keys s) + 1

step :: Σ -> Σ
-- Variable
step (Ref x, ρ, σ, κ) = (Lam lam, ρ', σ, κ) where Clo(lam, ρ') = σ!(ρ!x)
-- Application
step (f :@ e, ρ, σ, κ) = (f, ρ, σ', κ')
  where a' = alloc(σ)
        σ' = σ // [a' ==> Cont κ]
        κ' = Arg(e, ρ, a')
-- Argument Evaluation Cont
step (Lam lam, ρ, σ, Arg(e, ρ', a')) = (e, ρ', σ, App(lam, ρ, a'))
-- Application Cont
step (Lam lam, ρ, σ, App(x :=> e, ρ', a)) = 
  (e, ρ' // [x ==> a'], σ // [a' ==> Clo(lam, ρ)], κ) 
  where a' = alloc(σ)
        Cont κ = σ ! a

inject :: Exp -> Σ
inject (e) = (e, Data.Map.empty, Data.Map.empty, Done)

collect :: (a -> a) -> (a -> Bool) -> a -> [a]
collect f isFinal ς0 | isFinal ς0 = [ς0]
                     | otherwise = ς0 : (collect f isFinal (f(ς0)))

isFinal :: Σ -> Bool
isFinal (Lam _, _, _, Done) = True
isFinal _ = False

evaluate :: Exp -> [Σ]
evaluate e = collect step isFinal (inject(e))

states = evaluate (Lam("x" :=> (Ref "x")) :@ Lam("y" :=> (Ref "y")))
