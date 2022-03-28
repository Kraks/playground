module Main where

-- https://www.zinkov.com/posts/2015-08-25-building-a-probabilisitic-interpreter/

import Data.List hiding (empty, insert, map)
import Control.Monad

import Data.HashMap.Strict hiding (map)
import System.Random.MWC as MWC
import System.Random.MWC.Distributions as MD

type Name = String
type Env  = HashMap String Val

data Val =
    D Double
  | B Bool
  | F (Val -> Val)
  | P Val Val

instance Show Val where
  show (D x) = show x
  show (B b) = show b
  show (F _) = "<function>"
  show (P x y) = "<" ++ show x ++ ", " ++ show y ++ ">"

instance Eq Val where
  D x == D y = x == y
  B x == B y = x == y
  P x1 x2 == P y1 y2 = x1 == y1 && x2 == y2
  _ == _ = False

instance Ord Val where
  D x <= D y = x <= y
  B x <= B y = x <= y
  P x1 x2 <= P y1 y2 = x1 <= y1 && x2 <= y2
  _ <= _ = error "comparing functions undefined"

data Expr =
    Lit Double
  | Var Name
  | Pair Expr Expr
  | Fst Expr
  | Snd Expr
  | If Expr Expr Expr
  | Eql Expr Expr
  | Les Expr Expr
  | Gre Expr Expr
  | And Expr Expr
  | Lam Name Expr
  | App Expr Expr
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  deriving (Eq, Show)

evalT :: Expr -> Env -> Val
evalT (Lit a) _            = D a
evalT (Var x)      env     = env ! x
evalT (Lam x body) env     = F (\ x' -> evalT body (insert x x' env))
evalT (App f x)    env     = app (evalT f env) (evalT x env)
evalT (Eql x y)    env     = B $ (evalT x env) == (evalT y env)
evalT (Les x y)    env     = B $ (evalT x env) <= (evalT y env)
evalT (Gre x y)    env     = B $ (evalT x env) >= (evalT y env)
evalT (And x y)    env     = liftB (&&) (evalT x env) (evalT y env)
evalT (Add x y)    env     = liftOp (+) (evalT x env) (evalT y env)
evalT (Sub x y)    env     = liftOp (-) (evalT x env) (evalT y env)
evalT (Mul x y)    env     = liftOp (*) (evalT x env) (evalT y env)
evalT (Div x y)    env     = liftOp (/) (evalT x env) (evalT y env)
evalT (Pair x y)   env     = P (evalT x env) (evalT y env)
evalT (Fst x)      env     = fst_ $ evalT x env
 where fst_ (P a b)        = a
evalT (Snd x)      env     = snd_ $ evalT x env
 where snd_ (P a b)        = b
evalT (If b t f)   env     = if_ (evalT b env) (evalT t env) (evalT f env)
 where if_ (B True)  t' f' = t'
       if_ (B False) t' f' = f'

app :: Val -> Val -> Val
app (F f') x' = f' x'

liftOp :: (Double -> Double -> Double) -> Val -> Val -> Val
liftOp op (D e1) (D e2) = D (op e1 e2)

liftB  :: (Bool -> Bool -> Bool) -> Val -> Val -> Val
liftB  op (B e1) (B e2) = B (op e1 e2)

-- Measure: un-normalized probability distributions
-- 1. continuous uniform distrubution, bounded by expressions
-- 2. weighted distribution, returns the value of its second argument at prob of the first argument
-- 3. bind takes a measure as input, and a function from draws in that measure to another measure

data Meas =
    Uniform Expr Expr
  | Weight Expr Expr
  | Bind Name Meas Meas
  deriving (Eq, Show)

dirac :: Expr -> Meas
dirac x = Weight (Lit 1.0) x

-- x <~ uniform (1, 5)
-- return x + x
prog1 = Bind "x" (Uniform (Lit 1) (Lit 5))
        (dirac (Add (Var "x") (Var "x")))

-- Measures are evaluated by producing a weighted sample from the measure space
-- also called importance sampling
evalM :: Meas -> Env -> MWC.GenIO -> IO (Val, Double)
evalM (Uniform lo hi) env g = do
  let D lo' = evalT lo env
  let D hi' = evalT hi env
  x <- MWC.uniformR (lo', hi') g
  return (D x, 1.0)
evalM (Weight i x) env g = do
  let D i' = evalT i env
  return (evalT x env, i')
evalM (Bind x m f) env g = do
  (m', w1) <- evalM m env g
  let env' = insert x m' env
  (f', w2) <- evalM f env' g
  return (f', w1 * w2)

test1 :: IO ()
test1 = do
  g <- MWC.createSystemRandom
  draw <- evalM prog1 empty g
  print draw

-- conditional distributions

data Cond =
    UCond Meas
  | UniformC Expr Expr Expr
  | WeightC Expr Expr Expr
  | BindC Name Cond Cond

evalC :: Cond -> Meas
evalC (UCond m) = m
evalC (UniformC lo hi x) = Weight (If (And (Gre x lo)
                                           (Les x hi))
                                      (Div x (Sub hi lo))
                                      (Lit 0)) x
evalC (WeightC i x y) = Weight (If (Eql x y)
                                   i
                                   (Lit 0)) y
evalC (BindC x m f) = Bind x (evalC m) (evalC f)

-- What’s the conditional distribution on x given y is 3?
prog2 = BindC "x" (UCond (Uniform (Lit 1) (Lit 5)))      -- x <~ uniform(1, 5)
         (BindC "_" (UniformC (Var "x") (Lit 7) (Lit 3)) -- y <~ uniform(x, 7)
                                                         -- observe y 3
          (UCond (dirac (Var "x"))))                     -- return x

test2 :: IO ()
test2 = do
   g <- MWC.createSystemRandom
   samples <- replicateM 10 (evalM (evalC prog2) empty g)
   print samples

main :: IO ()
main = test2
