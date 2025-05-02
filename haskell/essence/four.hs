-- Output
import Prelude hiding (lookup)

type O a = (String, a)

unitO a = ("", a)

m `bindO` k = let (r, a) = m
                  (s, b) = k a
              in (r ++ s, b)

showO (s, a) = "Output: " ++ s ++ " Value: " ++ showval a

outO :: Value -> O ()
outO a = (showval a ++ "; ", ())

----------

type Name = String

data Term = Var String
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term
          | Out Term

data Value = Wrong
           | Num Int
           | Fun (Value -> O Value)

type Env = [(Name, Value)]

showval :: Value -> String
showval Wrong = "<wrong>"
showval (Num i) = show i
showval (Fun f) = "<function>"

interp :: Term -> Env -> O Value
interp (Var x) e = lookup x e
interp (Con i) e = unitO (Num i)
interp (Add u v) e = interp u e `bindO` (\a ->
                     interp v e `bindO` (\b ->
                     add a b))
interp (Lam x v) e = unitO (Fun (\a -> interp v ((x, a):e)))
interp (App t u) e = interp t e `bindO` (\f ->
                     interp u e `bindO` (\a ->
                     apply f a))
interp (Out u) e = interp u e `bindO` (\a ->
                   outO a `bindO` (\() ->
                   unitO a))

lookup :: Name -> Env -> O Value
lookup x [] = unitO Wrong
lookup x ((y,v):e) = if x == y then unitO v else lookup x e

add :: Value -> Value -> O Value
add (Num i) (Num j) = unitO (Num (i + j))
add a b = unitO Wrong

apply :: Value -> Value -> O Value
apply (Fun k) a = k a
apply f a = unitO Wrong

test :: Term -> String
test t = showO (interp t [])

-------

term0 = (App (Lam "x" (Add (Var "x") (Var "x")))
             (Add (Con 10) (Con 11)))

term1 = (App (Con 1) (Con 2))

term2 = (Add (Con 12) (Add (Con 10) (Con 11)))

term3 = (Add (Out (Con 41)) (Add (Out (Con 1)) (Out (Con 2))))
