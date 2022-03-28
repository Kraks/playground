-- Backward State

import Prelude hiding (lookup)

type State = Int

type S a = State -> (a, State)

unitS :: a -> s -> (a, s)
unitS a = \s0 -> (a, s0)

bindS :: (s -> (a, s)) -> (a -> s -> (b, s)) -> s -> (b, s)
m `bindS` k = \s2 -> let (a, s0) = m s1
                         (b, s1) = k a s2
                     in (b, s0)

showS m = let (a, s1) = m 0
          in "Value: " ++ showval a ++ "; " ++
             "Count: " ++ show s1

tickS :: S ()
tickS = \s -> ((), s+1)

fetchS :: S State
fetchS = \s -> (s, s)

----------

type Name = String

data Term = Var String
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term
          | Count

data Value = Wrong
           | Num Int
           | Fun (Value -> S Value)

type Env = [(Name, Value)]

showval :: Value -> String
showval Wrong = "<wrong>"
showval (Num i) = show i
showval (Fun f) = "<function>"

interp :: Term -> Env -> S Value
interp (Var x) e = lookup x e
interp (Con i) e = unitS (Num i)
interp (Add u v) e = interp u e `bindS` (\a ->
                     interp v e `bindS` (\b ->
                     add a b))
interp (Lam x v) e = unitS (Fun (\a -> interp v ((x, a):e)))
interp (App t u) e = interp t e `bindS` (\f ->
                     interp u e `bindS` (\a ->
                     apply f a))
interp (Count) e = fetchS `bindS` (\i -> unitS (Num i))

lookup :: Name -> Env -> S Value
lookup x [] = unitS Wrong
lookup x ((y,v):e) = if x == y then unitS v else lookup x e

add :: Value -> Value -> S Value
add (Num i) (Num j) = tickS `bindS` (\() -> unitS (Num (i + j)))
add a b = unitS Wrong

apply :: Value -> Value -> S Value
apply (Fun k) a = tickS `bindS` (\() -> k a)
apply f a = unitS Wrong

test :: Term -> String
test t = showS (interp t [])

-------

term0 = (App (Lam "x" (Add (Var "x") (Var "x")))
             (Add (Con 10) (Con 11)))

term1 = (App (Con 1) (Con 2))

term2 = (Add (Con 12) (Add (Con 10) (Con 11)))

term3 = (Add (Add (Con 1) (Con 2)) Count)
