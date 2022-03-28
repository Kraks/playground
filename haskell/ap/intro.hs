import Prelude hiding (sequence, repeat)

-- Sequencing commands

sequence :: [IO a] -> IO [a]
sequence [] = return []
sequence (c : cs) = do
  x <- c
  xs <- sequence cs
  return (x : xs)

ap :: Monad m => m (a -> b) -> m a -> m b
ap mf mx = do
  f <- mf
  x <- mx
  return (f x)

sequence' :: [IO a] -> IO [a]
sequence' [] = return []
sequence' (c : cs) = return (:) `ap` c `ap` (sequence' cs)

-- 1.2 Transposing matrices

transpose :: [[a]] -> [[a]]
transpose [] = []
transpose (xs : xss) = zipWith (:) xs (transpose xss)

repeat :: a -> [a]
repeat x = x : repeat x

zapp :: [a -> b] -> [a] -> [b]
zapp (f : fs) (x : xs) = f x : zapp fs xs
zapp _        _        = []

transpose' :: [[a]] -> [[a]]
transpose' [] = repeat []
transpose' (xs : xss) = repeat (:) `zapp` xs `zapp` (transpose xss)

-- 1.3 Evaluating expressions

data Exp v = Var v
           | Val Int
           | Add (Exp v) (Exp v)

type Env v = [(v, Int)]

fetch :: a -> [(a, Int)] -> Int
fetch = undefined

eval :: Exp v -> Env v -> Int
eval (Var x) env = fetch x env
eval (Val x) env = x
eval (Add p q) env = eval p env + eval q env
