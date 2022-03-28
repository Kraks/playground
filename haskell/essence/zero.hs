-- Normal interpreter with identity monad

import Prelude hiding (lookup)

type I a = a

unitI a = a
a `bindI` k = k a
showI a = showval a

type Name = String

data Term = Var Name
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term

data Value = Wrong
           | Num Int
           | Fun (Value -> I Value)

type Env = [(Name, Value)]

showval :: Value -> String
showval Wrong = "<wrong>"
showval (Num i) = show i
showval (Fun f) = "<function>"

interp :: Term -> Env -> I Value
interp (Var x) e = lookup x e
interp (Con i) e = unitI (Num i)
interp (Add u v) e = interp u e `bindI` (\a ->
                     interp v e `bindI` (\b ->
                     add a b))
interp (Lam x v) e = unitI (Fun (\a -> interp v ((x, a):e)))
interp (App t u) e = interp t e `bindI` (\f ->
                     interp u e `bindI` (\a ->
                     apply f a))

lookup :: Name -> Env -> I Value
lookup x [] = unitI Wrong
lookup x ((y,v):e) = if x == y then unitI v else lookup x e

add :: Value -> Value -> I Value
add (Num i) (Num j) = unitI (Num (i + j))
add a b = unitI Wrong

apply :: Value -> Value -> I Value
apply (Fun k) a = k a
apply f a = unitI Wrong

test :: Term -> String
test t = showI (interp t [])
