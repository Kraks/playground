-- CPS interpreter
import Prelude hiding (lookup)

type Answer = Value

type K a = (a -> Answer) -> Answer

unitK a = \c -> c a

m `bindK` k = \c -> m (\a -> k a c)

showK m = showval (m (\x -> x))

---------

type Name = String

data Term = Var Name
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term
          | CallCC Name Term

data Value = Wrong
           | Num Int
           | Fun (Value -> K Value)

type Env = [(Name, Value)]

showval :: Value -> String
showval Wrong = "<wrong>"
showval (Num i) = show i
showval (Fun f) = "<function>"

interp :: Term -> Env -> K Value
interp (Var x) e = \c -> lookup x e c
interp (Con i) e = \c -> c (Num i)
interp (Add u v) e = \c -> interp u e (\a ->
                           interp v e (\b ->
                           add a b c))
interp (Lam x v) e = \c -> c (Fun (\a -> interp v ((x,a):e)))
interp (App t u) e = \c -> interp t e (\f ->
                           interp u e (\a ->
                           apply f a c))
interp (CallCC x v) e = callccK (\k -> interp v ((x, Fun k):e))

callccK :: ((a -> (b -> Answer) -> Answer) -> (a -> Answer) -> Answer) -> (a -> Answer) -> Answer
--callccK :: ((a -> K b) -> K a) -> K a
-- c :: (a->Answer)
-- c a :: Answer
-- \d -> c a :: d -> a
-- k :: a -> d -> a
callccK h = \c -> let k a = \d -> c a in h k c

lookup :: Name -> Env -> K Value
lookup x [] = \c -> c Wrong
lookup x ((y,v):e) = \c -> if x == y then c v else lookup x e c

add :: Value -> Value -> K Value
add (Num i) (Num j) = \c -> c (Num (i + j))
add a b = \c -> c Wrong

apply :: Value -> Value -> K Value
apply (Fun k) a = \c -> k a c
apply f a = \c -> c Wrong

test :: Term -> String
test t = showK (interp t [])

term0 = (Add (Con 1) (CallCC "k" (Add (Con 2) (App (Var "k") (Con 4)))))
