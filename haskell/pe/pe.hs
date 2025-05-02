-- A Partial Evaluator

import Data.Maybe
import Data.Hashable (hash)
import Control.Monad.State
import Prelude hiding (exp)

type Prog = ([FDef], Expr)
type FDef = (String, ([String], Expr))

data Val = IVal { getInt  :: Int }
         | BVal { getBool :: Bool}
         deriving Show

data Expr = Const { getVal :: Val }
          | Var String
          | Apply String [Expr]
          | Prim Op [Expr]
          | If Expr Expr Expr
          deriving Show

data Op = Equal | Add | Sub | Mul deriving Show

type Env = [(String, Val)]

peval :: Prog -> Prog
peval (fdefs, main) = swap (runState (peval' main []) [])
  where
    peval' :: Expr -> Env -> State [FDef] Expr
    peval' (Const v) env = return (Const v)
    peval' (Var s) env = 
      case lookup s env of
        Just e -> return (Const e)
        Nothing -> return (Var s)
    peval' (Prim op es) env = do
      rs <- mapM (flip peval' env) es
      if all isVal rs
         then return (Const (prim op (map getVal rs)))
         else return (Prim op rs)
    peval' (If cnd thn els) env = do
      r0 <- peval' cnd env
      if isVal r0 then
         if getBool (getVal r0)
            then peval' thn env
            else peval' els env
          else do
            r1 <- peval' thn env
            r2 <- peval' els env
            return (If r0 r1 r2)
    peval' (Apply s es) env = do 
      let (ss, body) = fromJust (lookup s fdefs)
      rs <- mapM (flip peval' env) es
      let z = zip ss rs
      let statics = [ (s, getVal r) | (s, r) <- z, isVal r ]
      let dynamics = [ (s, v) | (s, v) <- z, not (isVal v) ]
      if null dynamics then
        peval' body statics
        else do
          let s' = s ++ (show $ hash (show statics))
          fdefs <- get 
          when (isNothing (lookup s' fdefs)) (do 
            put (fdefs ++ [(s', undefined)])
            e' <- peval' body statics
            modify (update (const (map fst dynamics, e')) s'))
          return (Apply s' (map snd dynamics))

prim Equal [IVal i1, IVal i2] = BVal (i1 == i2)
prim Add   [IVal i1, IVal i2] = IVal (i1 + i2)
prim Sub   [IVal i1, IVal i2] = IVal (i1 - i2)
prim Mul   [IVal i1, IVal i2] = IVal (i1 * i2)

isVal (Const v) = True
isVal _ = False

swap (a, b) = (b, a)

update :: Eq k => (v -> v) -> k -> [(k, v)] -> [(k, v)]
update f k ((k',v):kvs) = if k == k' then (k', f v):kvs else (k',v):update f k kvs

-- a test program
-- exp(x, n) = if n == 0 then 1 else x * exp(x, n - 1)
exp = ("exp", (["x", "n"],
      If (Prim Equal [Var "n", Const (IVal 0)])
         (Const (IVal 1))
         (Prim Mul [Var "x", Apply "exp" [Var "x", Prim Sub [Var "n", Const (IVal 1)]]])))

exp_3 = peval ([exp], Apply "exp" [Var "x", Const (IVal 3)])


