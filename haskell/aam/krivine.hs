-- A call-by-name Krivine's machine
-- Section 4, Systematic abstraction of abstract machine

{-# LANGUAGE TypeOperators, TypeSynonymInstances #-}
import Data.Map

type Addr = Int
type Var = String
type Env = Var :-> Addr
type k :-> v = Data.Map.Map k v
type Store = Addr :-> Storable
type Σ = (Exp, Env, Store, Kont)

data Lambda = Var :=> Exp

data Exp = Ref Var
         | Lam Lambda
         | Exp :@ Exp

data Storable = Thunk (Exp, Env)
              | Clo (Lambda, Env)

data Kont = Done 
          | C1(Addr, Kont) 
          | C2(Addr, Kont)

instance Show Lambda where 
  show (v :=> e) = "<λ" ++ v ++ "." ++ show e ++ ">"

instance Show Exp where
  show (Ref v) = v
  show (Lam lam) = show lam
  show (e1 :@ e2) = "<" ++ show e1 ++ " " ++ show e2 ++ ">"

instance Show Storable where 
  show (Clo(lam, env)) = "Clo<" ++ show lam ++ "," ++ show env ++ ">"
  show (Thunk(exp, env)) = "Thunk<" ++ show exp ++ "," ++ show env ++ ">"
  
instance Show Kont where
  show Done = "Done"
  show (C1(addr, k)) = "C1<" ++ show addr ++ "," ++ show k ++ ">"
  show (C2(addr, k)) = "C2<" ++ show addr ++ "," ++ show k ++ ">"

-- make a tuple
(==>) :: a -> b -> (a, b)
(==>) x y = (x, y)

-- insert into a map
(//) :: Ord a => (a :-> b) -> [(a, b)] -> (a :-> b)
(//) m [(x, y)] = Data.Map.insert x y m

alloc :: Store -> Addr
alloc(s) = (Prelude.foldl max 0 $ keys s) + 1

step :: Σ -> Σ
step (Ref x, ρ, σ, κ) = 
  let v = σ!(ρ!x) in case v of Thunk(exp, ρ') -> (exp, ρ', σ, C1(ρ!x, κ))
                               Clo(v, ρ') -> (Lam v, ρ', σ, κ)
step (f :@ e, ρ, σ, κ) = (f, ρ, σ', κ')
  where a  = alloc(σ)
        σ' = σ // [a ==> Thunk(e, ρ)]
        κ' = C2(a, κ)
step (Lam lam, ρ, σ, C1(a, κ)) = (Lam lam, ρ, σ // [a ==> Clo(lam, ρ)], κ)
step (Lam (x :=> e), ρ, σ, C2(a, κ)) = (e, ρ // [x ==> a], σ , κ)

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
