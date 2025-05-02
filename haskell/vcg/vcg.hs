module Main where

import System.IO
import Control.Monad.State

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List

type Ident = String

data Exp = Lit Int
         | Var Ident
         | Plus Exp Exp
         | Minus Exp Exp
         | Mult Exp Exp
         | Div Exp Exp

data Pred = T | F
          | Eq Exp Exp
          | Le Exp Exp
          | Lt Exp Exp
          | Ge Exp Exp
          | Gt Exp Exp
          | And Pred Pred
          | Or Pred Pred
          | Not Pred
          | Implies Pred Pred
          | Assume Pred
          | Assert Pred
          | Invariant Pred

data Com = Asgn Ident Exp
         | Seq Com Com
         | If Pred Com Com
         | While Pred Pred Com -- while test inv body
         | Skip

type VC = State [Pred]

smtValid :: Pred -> Bool
smtValid = undefined --TODO: call a SMT solver

verify :: Pred -> Com -> Pred -> Bool
verify p c q = all smtValid queries
  where (q', conds) = runState (vcgen c q) []
        queries     = p `Implies` q' : conds

toSmt :: FilePath -> Pred -> Com -> Pred -> IO ()
toSmt filename p c q = do
  let (q', conds) = runState (vcgen c q) []
      queries = p `Implies` q' : conds
      allVars = Set.union (Set.union (getVarsFromPred p) (getVarsFromCom c)) (getVarsFromPred q)
      content = queryToSmt allVars queries
  writeFile filename content

declareConst :: String -> String -> String
declareConst ty v = "(declare-const " ++ v ++ " " ++ ty ++ ")"

assertPred :: Pred -> String
assertPred p = "(push)\n" ++
               "(assert (not " ++ (predToSmtRepr p) ++ "))\n" ++
               "(check-sat)\n" ++
               "(pop)"

queryToSmt :: Set String -> [Pred] -> String
queryToSmt vars preds =
  let declares = Set.map (declareConst "Int") vars
      asserts = map assertPred preds
   in (List.intercalate "\n" $ Set.toList declares) ++ "\n" ++
      (List.intercalate "\n" asserts)

substExp :: Exp -> (Ident, Exp) -> Exp
substExp (Lit i) _                  = Lit i
substExp (Var v') (v,e) | v' == v   = e
substExp (Var v') _     | otherwise = Var v'
substExp (Plus e1 e2) ve            = Plus (substExp e1 ve) (substExp e2 ve)
substExp (Minus e1 e2) ve           = Minus (substExp e1 ve) (substExp e2 ve)
substExp (Mult e1 e2) ve            = Mult (substExp e1 ve) (substExp e2 ve)
substExp (Div e1 e2) ve             = Div (substExp e1 ve) (substExp e2 ve)

subst :: Pred -> (Ident, Exp) -> Pred
subst (T) _              = (T)
subst (F) _              = (F)
subst (Eq e1 e2) ve      = Eq (substExp e1 ve) (substExp e2 ve)
subst (Le e1 e2) ve      = Le (substExp e1 ve) (substExp e2 ve)
subst (Lt e1 e2) ve      = Lt (substExp e1 ve) (substExp e2 ve)
subst (Ge e1 e2) ve      = Ge (substExp e1 ve) (substExp e2 ve)
subst (Gt e1 e2) ve      = Gt (substExp e1 ve) (substExp e2 ve)
subst (And p1 p2) ve     = And (subst p1 ve) (subst p2 ve)
subst (Or p1 p2) ve      = Or (subst p1 ve) (subst p2 ve)
subst (Not p) ve         = Not (subst p ve)
subst (Implies p1 p2) ve = Implies (subst p1 ve) (subst p2 ve)
subst (Assume p) ve      = Assume (subst p ve)
subst (Assert p) ve      = Assert (subst p ve)
subst (Invariant p) ve   = Invariant (subst p ve)

getVarsFromExp :: Exp -> Set String
getVarsFromExp (Lit _)       = Set.empty
getVarsFromExp (Var v)       = Set.singleton v
getVarsFromExp (Plus e1 e2)  = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromExp (Minus e1 e2) = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromExp (Mult e1 e2)  = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromExp (Div e1 e2)   = Set.union (getVarsFromExp e1) (getVarsFromExp e2)

getVarsFromPred :: Pred -> Set String
getVarsFromPred (T)             = Set.empty
getVarsFromPred (F)             = Set.empty
getVarsFromPred (Eq e1 e2)      = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromPred (Le e1 e2)      = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromPred (Lt e1 e2)      = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromPred (Ge e1 e2)      = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromPred (Gt e1 e2)      = Set.union (getVarsFromExp e1) (getVarsFromExp e2)
getVarsFromPred (And p1 p2)     = Set.union (getVarsFromPred p1) (getVarsFromPred p2)
getVarsFromPred (Or p1 p2)      = Set.union (getVarsFromPred p1) (getVarsFromPred p2)
getVarsFromPred (Not p)         = getVarsFromPred p
getVarsFromPred (Implies p1 p2) = Set.union (getVarsFromPred p1) (getVarsFromPred p2)
getVarsFromPred (Assume p)      = getVarsFromPred p
getVarsFromPred (Assert p)      = getVarsFromPred p
getVarsFromPred (Invariant p)   = getVarsFromPred p

getVarsFromCom :: Com -> Set String
getVarsFromCom (Asgn i e)    = Set.insert i (getVarsFromExp e)
getVarsFromCom (Seq c1 c2)   = Set.union (getVarsFromCom c1) (getVarsFromCom c2)
getVarsFromCom (If p c1 c2)  = Set.union (Set.union (getVarsFromPred p) (getVarsFromCom c1)) (getVarsFromCom c2)
getVarsFromCom (While b i c) = Set.union (Set.union (getVarsFromPred b) (getVarsFromPred i)) (getVarsFromCom c)
getVarsFromCom (Skip)        = Set.empty

expToSmtRepr :: Exp -> String
expToSmtRepr (Lit i)       = show i
expToSmtRepr (Var v)       = v
expToSmtRepr (Plus e1 e2)  = "(+ " ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
expToSmtRepr (Minus e1 e2) = "(- " ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
expToSmtRepr (Mult e1 e2)  = "(* " ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
expToSmtRepr (Div e1 e2)   = "(/ " ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"

predToSmtRepr :: Pred -> String
predToSmtRepr T               = "true"
predToSmtRepr F               = "false"
predToSmtRepr (Eq e1 e2)      = "(= "  ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
predToSmtRepr (Le e1 e2)      = "(<= " ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
predToSmtRepr (Lt e1 e2)      = "(< "  ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
predToSmtRepr (Ge e1 e2)      = "(>= " ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
predToSmtRepr (Gt e1 e2)      = "(> "  ++ (expToSmtRepr e1) ++ " " ++ (expToSmtRepr e2) ++ ")"
predToSmtRepr (And p1 p2)     = "(and "  ++ (predToSmtRepr p1) ++ " " ++ (predToSmtRepr p2) ++ ")"
predToSmtRepr (Or p1 p2)      = "(Or "  ++ (predToSmtRepr p1) ++ " " ++ (predToSmtRepr p2) ++ ")"
predToSmtRepr (Not p)         = "(not " ++ (predToSmtRepr p) ++ ")"
predToSmtRepr (Implies p1 p2) = "(=> " ++ (predToSmtRepr p1) ++ " " ++ (predToSmtRepr p2) ++ ")"
predToSmtRepr (Assume p)      = predToSmtRepr p
predToSmtRepr (Assert p)      = predToSmtRepr p
predToSmtRepr (Invariant p)   = predToSmtRepr p

sc :: Pred -> VC ()
sc p = modify $ \conds -> p : conds

-- TODO: strengthen precondition or weaken postcondition?
-- TODO: capture-avoiding substitution

-- Given a command and a postcondition, infer its weakest precondition and VC
vcgen :: Com -> Pred -> VC Pred
vcgen (Skip) q = return q
vcgen (Asgn x e) q = return $ q `subst` (x, e)
vcgen (Seq s1 s2) q = vcgen s1 =<< vcgen s2 q
vcgen (If b c1 c2) q = do
  q1 <- vcgen c1 q
  q2 <- vcgen c2 q
  return $ (b `Implies` q1) `And` ((Not b) `Implies` q2)
vcgen (While b i c) q = do
  q' <- vcgen c i
  sc $ (i `And` b) `Implies` q'      -- I && B -> Q'
  sc $ (i `And` (Not b)) `Implies` q -- I && not B -> Q
  return $ i

{--
assume x == 8 && y == 16
while (x > 0) {
  invariant y = 2 * x && x >= 0
  x = x - 1
  y = y - 2
}
assert y == 0
--}

example1 :: Com
example1 = While ((Var "x") `Gt` (Lit 0))
                 (Invariant $ ((Var "y") `Eq` (Mult (Lit 2) (Var "x")))
                              `And` ((Var "x") `Ge` (Lit 0)))
                 (Seq (Asgn "x" (Minus (Var "x") (Lit 1)))
                      (Asgn "y" (Minus (Var "y") (Lit 2))))

main :: IO ()
main = toSmt "output.z3"
             (Assume $ ((Var "x") `Eq` (Lit 8)) `And` ((Var "y") `Eq` (Lit 16)))
             example1
             (Assert $ (Var "y") `Eq` (Lit 0))
