-- Non-Deterministic Choice
import Prelude hiding (lookup)

type L a = [a]

unitL a = [a]

m `bindL` k = [b | a <- m, b <- k a]

zeroL = []

l `plusL` m = l ++ m

showL m = show [showval a | a <- m]

----------

type Name = String

data Term = Var String
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term
          | Fail
          | Amb Term Term

data Value = Wrong
           | Num Int
           | Fun (Value -> L Value)

type Env = [(Name, Value)]

showval :: Value -> String
showval Wrong = "<wrong>"
showval (Num i) = show i
showval (Fun f) = "<function>"

interp :: Term -> Env -> L Value
interp (Var x) e = lookup x e
interp (Con i) e = unitL (Num i)
interp (Add u v) e = interp u e `bindL` (\a ->
                     interp v e `bindL` (\b ->
                     add a b))
interp (Lam x v) e = unitL (Fun (\a -> interp v ((x, a):e)))
interp (App t u) e = interp t e `bindL` (\f ->
                     interp u e `bindL` (\a ->
                     apply f a))
interp Fail e = zeroL
interp (Amb u v) e = interp u e `plusL` interp v e

lookup :: Name -> Env -> L Value
lookup x [] = unitL Wrong
lookup x ((y,v):e) = if x == y then unitL v else lookup x e

add :: Value -> Value -> L Value
add (Num i) (Num j) = unitL (Num (i + j))
add a b = unitL Wrong

apply :: Value -> Value -> L Value
apply (Fun k) a = k a
apply f a = unitL Wrong

test :: Term -> String
test t = showL (interp t [])

-------

term0 = (App (Lam "x" (Add (Var "x") (Var "x")))
             (Add (Con 10) (Con 11)))

term1 = (App (Con 1) (Con 2))

term2 = (Add (Con 12) (Add (Con 10) (Con 11)))

term3 = (App (Lam "x" (Add (Var "x") (Var "x")))
             (Amb (Con 1) (Con 2)))
