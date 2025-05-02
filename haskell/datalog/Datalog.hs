-- https://dodisturb.me/posts/2018-12-25-The-Essence-of-Datalog.html

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

import Data.Function (fix)
import Data.List (nub, intercalate, isSubsequenceOf)
import Data.Maybe (mapMaybe, fromMaybe, isNothing)

data Rule = Rule {
  _head :: Atom,
  _body :: [Atom]
} deriving Show

data Atom = Atom {
  _predSym :: String,
  _terms :: [Term]
} deriving (Eq, Show)

data Term = Var String
          | Sym String
  deriving (Eq, Show)

-- ancestor(X, Z) :- advisor(X, Y), ancestor(Y, Z)
ancestor_rule :: Rule
ancestor_rule = Rule (Atom "ancestor" [Var "X", Var "Z"])
                     [Atom "advisor"  [Var "X", Var "Y"],
                      Atom "ancestor" [Var "Y", Var "Z"]]

-- a fact
fact1 :: Rule
fact1 = Rule (Atom "advisor" [Sym "Andrew Rice", Sym "Mistral Contrastin"]) []

type Program = [Rule]

type KnowledgeBase = [Atom]

type Substitution = [(Term, Term)]

mtSubst :: Substitution
mtSubst = []

substitute :: Atom -> Substitution -> Atom
substitute atom subst = atom { _terms = map go (_terms atom) }
  where go sym@Sym{} = sym
        go var@Var{} = fromMaybe var (var `lookup` subst)

unify :: Atom -> Atom -> Maybe Substitution
unify (Atom predSym ts) (Atom predSym' ts')
  | predSym == predSym' = go $ zip ts ts'
  | otherwise           = Nothing
  where go :: Substitution -> Maybe Substitution
        go [] = Just mtSubst
        go ((s@Sym{}, s'@Sym{}) : rest) = if s == s' then go rest else Nothing
        go ((v@Var{},  s@Sym{}) : rest) = do
          incompleteSubst <- go rest
          case v `lookup` incompleteSubst of
            Just s' | s /= s' -> Nothing
            _                 -> return $ (v, s) : incompleteSubst
        go ((_, Var{}) : _) = error "The second atom is assumed to be ground"

evalAtom :: KnowledgeBase -> Atom -> [Substitution] -> [Substitution]
evalAtom kb atom substs = do
  subst <- substs
  let groundAtom = substitute atom subst
  extension <- mapMaybe (unify groundAtom) kb
  return $ subst <> extension

walk :: KnowledgeBase -> [Atom] -> [Substitution]
walk kb = foldr (evalAtom kb) [mtSubst]

evalRule :: KnowledgeBase -> Rule -> KnowledgeBase
evalRule kb (Rule head body) = map (substitute head) (walk kb body)

immediateConsequence :: Program -> KnowledgeBase -> KnowledgeBase
immediateConsequence rules kb =
  nub . (kb <>) . concatMap (evalRule kb) $ rules

solve :: Program -> KnowledgeBase
solve rules =
  if all isRangeRestricted rules
    then fix step []
    else error "The input program is not range-restricted."
  where step :: (KnowledgeBase -> KnowledgeBase) -> KnowledgeBase -> KnowledgeBase
        step f kb =
          let kb' = immediateConsequence rules kb in
            if kb == kb' then kb else f kb'

isRangeRestricted :: Rule -> Bool
isRangeRestricted Rule{..} =
  (vars _head) `isSubsetof` (concatMap vars _body)
  where
    isSubsetof as bs = all (`elem` bs) as
    vars Atom{..} = nub $ filter (\case {Var{} -> True; _ -> False}) _terms

ancestor :: Program
ancestor =
  -- Facts
  fmap (\terms -> Rule (Atom "adviser" terms) [])
    [ [ Sym "Andrew Rice",     Sym "Mistral Contrastin" ]
    , [ Sym "Dominic Orchard", Sym "Mistral Contrastin" ]
    , [ Sym "Andy Hopper",     Sym "Andrew Rice" ]
    , [ Sym "Alan Mycroft",    Sym "Dominic Orchard" ]
    , [ Sym "David Wheeler",   Sym "Andy Hopper" ]
    , [ Sym "Rod Burstall",    Sym "Alan Mycroft" ]
    , [ Sym "Robin Milner",    Sym "Alan Mycroft" ]
    ] <>
  -- Actual rules
  [ Rule (Atom "academicAncestor" [ Var "X", Var "Y" ])
      [ Atom "adviser" [ Var "X", Var "Y" ] ]
  , Rule (Atom "academicAncestor" [ Var "X", Var "Z" ])
      [ Atom "adviser"          [ Var "X", Var "Y" ]
      , Atom "academicAncestor" [ Var "Y", Var "Z" ] ]
  ] <>
  -- Queries
  [ Rule (Atom "query1" [ Var "Intermediate" ])
      (fmap (Atom "academicAncestor")
        [ [ Sym "Robin Milner", Var "Intermediate" ]
        , [ Var "Intermediate", Sym "Mistral Contrastin" ] ])
  , Rule (Atom "query2" [ ])
      [ Atom "academicAncestor"
          [ Sym "Alan Turing", Sym "Mistral Contrastin" ] ]
  , Rule (Atom "query3" [ ])
      [ Atom "academicAncestor"
          [ Sym "David Wheeler", Sym "Mistral Contrastin" ] ]
  ]

query :: String -> Program -> [Substitution]
query predSym pr =
  case queryVarsL of
    [queryVars] -> zip queryVars <$> relevantKnowledgeBaseSyms
    [] -> error $ "The query '" ++ predSym ++ "' doesn't exists"
    _  -> error $ "The query '" ++ predSym ++ "' has multiple clauses"
  where
    relevantKnowledgeBase = filter ((== predSym) . _predSym) $ solve pr
    relevantKnowledgeBaseSyms = _terms <$> relevantKnowledgeBase
    queryRules = filter ((== predSym) . _predSym . _head) pr
    queryVarsL = _terms . _head <$> queryRules
