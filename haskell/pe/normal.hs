-- A Normal Interpreter
import Data.Maybe
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

-- a normal interpreter
eval :: Prog -> Val
eval (fdefs, main) = eval' main []
  where
    eval' :: Expr -> Env -> Val
    eval' (Const v) env = v
    eval' (Var s) env =
      case lookup s env of
        Just v -> v
        Nothing -> error "Undefined variable"
    eval' (Prim op es) env =
      let rs = [ eval' e env | e <- es ] in
        prim op rs
    eval' (If cnd thn els) env =
      if getBool (eval' cnd env)
         then eval' thn env
         else eval' els env
    eval' (Apply f es) env = 
      eval' body env' 
        where (ss, body) = fromJust (lookup f fdefs)
              env' = zip ss [ eval' e env | e <- es ]

prim Equal [IVal i1, IVal i2] = BVal (i1 == i2)
prim Add   [IVal i1, IVal i2] = IVal (i1 + i2)
prim Sub   [IVal i1, IVal i2] = IVal (i1 - i2)
prim Mul   [IVal i1, IVal i2] = IVal (i1 * i2)

-- a test program
-- exp(x, n) = if n == 0 then 1 else x * exp(x, n - 1)
exp = ("exp", (["x", "n"],
      If (Prim Equal [Var "n", Const (IVal 0)])
         (Const (IVal 1))
         (Prim Mul [Var "x", Apply "exp" [Var "x", Prim Sub [Var "n", Const (IVal 1)]]])))

eight = getInt $ eval ([exp], Apply "exp" [Const (IVal 2), Const (IVal 3)])


