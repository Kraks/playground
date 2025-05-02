-- Error handling with file position

import Prelude hiding (lookup)

data E a = Success a | Error String

unitE :: a -> E a
unitE a = Success a

errorE :: String -> E a
errorE s = Error s

bindE :: E a -> (a -> E b) -> E b
(Success a) `bindE` k = k a
(Error s) `bindE` k = Error s

showE :: E Value -> String
showE (Success a) = "Success: " ++ showval a
showE (Error s)   = "Error: " ++ s

---------

type Position = Int
type P a = Position -> E a

showpos :: Position -> String
showpos p = show p

unitP :: a -> t -> E a
unitP a = \p -> unitE a

errorP :: String -> Position -> E a
errorP s = \p -> errorE ("line " ++ showpos p ++ ": " ++ s)

bindP :: (p -> E a) -> (a -> p -> E b) -> p -> E b
m `bindP` k = \p -> m p `bindE` (\x -> k x p)

showP m = showE (m 0)

resetP :: Position -> P x -> P x
resetP q m = \p -> m q

---------

type Name = String

data Term = Var Name
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term
          | At Position Term

data Value = Wrong
           | Num Int
           | Fun (Value -> P Value)

type Env = [(Name, Value)]

showval :: Value -> String
showval Wrong = "<wrong>"
showval (Num i) = show i
showval (Fun f) = "<function>"

interp :: Term -> Env -> P Value
interp (Var x) e = lookup x e
interp (Con i) e = unitP (Num i)
interp (Add u v) e = interp u e `bindP` (\a ->
                     interp v e `bindP` (\b ->
                     add a b))
interp (Lam x v) e = unitP (Fun (\a -> interp v ((x, a):e)))
interp (App t u) e = interp t e `bindP` (\f ->
                     interp u e `bindP` (\a ->
                     apply f a))
interp (At p t) e = resetP p (interp t e)

lookup :: Name -> Env -> P Value
lookup x [] = unitP Wrong
lookup x ((y,v):e) = if x == y then unitP v else lookup x e

add :: Value -> Value -> P Value
add (Num i) (Num j) = unitP (Num (i + j))
add a b = errorP ("should be numbers: " ++ showval a ++ ", " ++ showval b)

apply :: Value -> Value -> P Value
apply (Fun k) a = k a
apply f a = errorP ("should be function: " ++ showval f)

test :: Term -> String
test t = showP (interp t [])

-------

term0 = (App (Lam "x" (Add (Var "x") (Var "x")))
             (Add (Con 10) (Con 11)))

term1 = (App (Con 1) (Con 2))

term2 = (At 82 (App (Lam "x" (Add (Var "z") (Var "x")))
                    (Add (Con 10) (Con 11))))
