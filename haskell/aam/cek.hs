-- CEK Machine
-- Section 2.2, Systematic abstraction of abstract machines

{-# LANGUAGE TypeOperators, TypeSynonymInstances #-}

import Data.Map

type Var = String
type Env = Var :-> D
type Σ = (Exp, Env, Cont)
type k :-> v = Data.Map.Map k v

data D = Clo(Lambda, Env)

data Lambda = Var :=> Exp

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp

data Cont = Done | Arg(Exp, Env, Cont) | App(Lambda, Env, Cont)

instance Show Exp where 
  show (Ref v) = v
  show (Lam lam) = show lam
  show (e1 :@ e2) = "<" ++ show e1 ++ " " ++ show e2 ++ ">"

instance Show Lambda where 
  show (v :=> e) = "<λ" ++ v ++ "." ++ show e ++ ">"

instance Show D where
  show (Clo(lam, e)) = "Clo<" ++ show lam ++ "," ++ show e ++ ">"

instance Show Cont where show k = showCont k
  show Done = "Done"
  show (Arg(e, env, k)) = "Arg<" ++ show e ++ "," ++ show env ++ "," ++ show k ++ ">"
  show (App(lam, env, k)) = "App<" ++ show lam ++ "," ++ show env ++ "," ++ show k ++ ">"

--showEnv e = (Data.Map.foldl (\acc (k, v) -> acc ++ k ++ "->" ++ show v) "[" e) ++ "]"
--instance Show Env where show e = showEnv e

-----
(==>) :: a -> b -> (a, b)
(==>) x y = (x, y)

(//) :: Ord a => (a :-> b) -> [(a, b)] -> (a :-> b)
(//) m [(x, y)] = Data.Map.insert x y m

step :: Σ -> Σ
-- Variable
step (Ref x, ρ, κ) = (Lam lam, ρ', κ) where Clo(lam, ρ') = ρ ! x
-- Application
step (f :@ e, ρ, κ) = (f, ρ, Arg(e, ρ, κ))
-- Argument Evaluation Cont
step (Lam lam, ρ, Arg(e, ρ', κ)) = (e, ρ', App(lam, ρ, κ))
-- Application Cont
step (Lam lam, ρ, App(x :=> e, ρ', κ)) = (e, ρ' // [x ==> Clo(lam, ρ)], κ)

inject :: Exp -> Σ
inject (e) = (e, Data.Map.empty, Done)

collect :: (a -> a) -> (a -> Bool) -> a -> [a]
collect f isFinal ς0 | isFinal ς0 = [ς0]
                     | otherwise = ς0 : (collect f isFinal (f(ς0)))

isFinal :: Σ -> Bool
isFinal (Lam _, ρ, Done) = True
isFinal _                = False

evaluate :: Exp -> [Σ]
evaluate e = collect step isFinal (inject(e))

states = evaluate (Lam("x" :=> (Ref "x")) :@ Lam("y" :=> (Ref "y")))
