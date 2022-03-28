module MiniTT where

import Prelude hiding ((*))

-- Expression

type Name = String

data Exp = ELam Patt Exp      -- λ-term
         | EUni               -- universe type
         | EPi Patt Exp Exp   -- Π type
         | ESig Patt Exp Exp  -- Σ type
         | EOne               -- 1 type
         | EUnit              -- unit
         | EPair Exp Exp      -- pair
         | ECon Name Exp      -- constructor
         | ESum Branch        -- labeled sum
         | EFun Branch        -- labeled λ-term
         | EFst Exp           -- first projection
         | ESnd Exp           -- second projection
         | EApp Exp Exp       -- application
         | EVar Name          -- variable
         | EVoid              -- void
         | ELet Decl Exp      -- declaration
         deriving (Eq, Ord, Show)

data Decl = Let Patt Exp Exp
          | Letrec Patt Exp Exp
          deriving (Eq, Ord, Show)

data Patt = PPair Patt Patt
          | PUnit
          | PVar Name
          deriving (Eq, Ord, Show)

type Branch = [(Name, Exp)]

-- Examples

boolType :: Exp
boolType = EUni

boolTerm :: Exp
boolTerm = ESum [("true", EUnit), ("false", EUnit)]

elimBoolType :: Exp
elimBoolType = EPi (PVar "C") (EPi PUnit (EVar "Bool") EUni)
                   (EPi PUnit (EApp (EVar "C") (EVar "false"))
                        (EPi PUnit (EApp (EVar "C") (EVar "true"))
                             (EPi (PVar "b") (EVar "Bool") (EApp (EVar "C") (EVar "b")))))

elimBoolTerm :: Exp
elimBoolTerm = ELam (PVar "C")
               (ELam (PVar "h0")
               (ELam (PVar "h1")
               (EFun [("true", ELam (PVar "_") (EVar "h1")),
                      ("false", ELam (PVar "_") (EVar "h0"))])))

idType :: Exp
idType = EPi (PVar "A") EUni (EPi PUnit (EVar "A") (EVar "A"))

idTerm :: Exp
idTerm = ELam (PVar "x") (EVar "x")

type SClos = (Branch, Env)

-- Function closures
data Clos = CloV Patt Exp Env
          | CloVCompose Clos Name
          deriving Show

-- Values

data Val = Lam Clos     -- closure value
         | Fun SClos    -- choices function
         | Pair Val Val -- pair
         | Con Name Val -- data constructor
         | Unit         -- unit value
         | Set          -- universe
         | One          -- unit type
         | Pi Val Clos  -- Π type
         | Sig Val Clos -- Σ type
         | Sum SClos    -- labeled sum
         | Nt Neut      -- neural value
         deriving Show

-- Neural values

data Neut = Gen Int
          | App Neut Val
          | Fst Neut
          | Snd Neut
          | NtFun SClos Neut
          deriving Show

-- Environment and operations

data Env = MtEnv
         | UpVar Env Patt Val
         | UpLet Env Decl
         deriving Show

inPat :: Name -> Patt -> Bool
inPat x (PVar y) = x == y
inPat x (PPair p1 p2) = inPat x p1 || inPat x p2
inPat _ PUnit = False

patProj :: Patt -> Name -> Val -> Val
patProj (PVar y) x v      | x == y = v
patProj (PPair p1 p2) x v | x `inPat` p1 = patProj p1 x (vfst v)
                          | x `inPat` p2 = patProj p2 x (vsnd v)
patProj _ _ _ = error "Not a pattern projection"

lookupEnv :: Env -> Name -> Val
lookupEnv (UpVar ρ pt v) x
  | x `inPat` pt = patProj pt x v
  | otherwise    = lookupEnv ρ x
lookupEnv (UpLet ρ (Let pt tp e)) x
  | x `inPat` pt = patProj pt x (eval e ρ)
  | otherwise    = lookupEnv ρ x
lookupEnv ρ0@(UpLet ρ (Letrec pt tp e)) x
  | x `inPat` pt = patProj pt x (eval e ρ0)
  | otherwise    = lookupEnv ρ x
lookupEnv MtEnv _ = error "empty environment"

-- Instantiation of a closure by a value
(*) :: Clos -> Val -> Val
(CloV pt e ρ) * v = eval e (UpVar ρ pt v)
(CloVCompose f c)  * v = f * Con c v

-- a closure composed with a constructor
(∘) :: Clos -> Name -> Clos
(∘) = CloVCompose

get :: (Eq a, Show a) => a -> [(a, b)] -> b
get s [] = error ("get " ++ show s)
get s ((s1, u) : us) | s == s1 = u
get s ((s1, u) : us)           = get s us

app :: Val -> Val -> Val
app (Lam f) v = f * v
app (Fun (brs, ρ)) (Con c v) = app (eval (get c brs) ρ) v
app (Fun s) (Nt k) = Nt (NtFun s k)
app (Nt k) m = Nt (App k m)
app e1 e2 = error $ "Not an application" ++ (show e1) ++ " " ++ (show e2)

vfst :: Val -> Val
vfst (Pair v1 _) = v1
vfst (Nt k) = Nt (Fst k)
vfst _ = error "Not a pair"

vsnd :: Val -> Val
vsnd (Pair _ v2) = v2
vsnd (Nt k) = Nt (Snd k)
vsnd _ = error "Not a pair"

eval :: Exp -> Env -> Val
eval e ρ = case e of
  EUni -> Set
  EOne -> One
  EUnit -> Unit
  EVar x -> lookupEnv ρ x
  ELet d e -> eval e (UpLet ρ d)
  ELam pt e -> Lam $ CloV pt e ρ
  EPi pt t b -> Pi (eval t ρ) $ CloV pt b ρ
  ESig pt t b -> Sig (eval t ρ) $ CloV pt b ρ
  EFst e -> vfst (eval e ρ)
  ESnd e -> vsnd (eval e ρ)
  EApp e1 e2 -> app (eval e1 ρ) (eval e2 ρ)
  EPair e1 e2 -> Pair (eval e1 ρ) (eval e2 ρ)
  ECon c e1 -> Con c (eval e1 ρ)
  ESum cas -> Sum (cas, ρ)
  EFun ces -> Fun (ces, ρ)
  _ -> error $ "cannot evaluate " ++ show e

-- Normal forms

data NExp = NUnit
          | NSet
          | NOne
          | NLam Int NExp
          | NPair NExp NExp
          | NCon Name NExp
          | NPi NExp Int NExp
          | NSig NExp Int NExp
          | NFun NSClos
          | NSum NSClos
          | NNt NNeut
          deriving (Show, Eq)

data NNeut = NGen Int
           | NApp NNeut NExp
           | NFst NNeut
           | NSnd NNeut
           | NNtFun NSClos NNeut
           deriving (Show, Eq)

type NSClos = (Branch, NEnv)

data NEnv = NMtEnv
          | NUpVar NEnv Patt NExp
          | NUpLet NEnv Decl
          deriving (Show, Eq)

-- Readback functions

genV :: Int -> Val
genV k = Nt (Gen k)

rbV :: Int -> Val -> NExp
rbV i v = case v of
  Set -> NSet
  Unit -> NUnit
  Lam f -> NLam i (rbV (i + 1) (f * genV i))
  Pair u v -> NPair (rbV i u) (rbV i v)
  Con c v -> NCon c (rbV i v)
  Pi t g -> NPi (rbV i t) i (rbV (i+1) (g * genV i))
  Sig t g -> NSig (rbV i t) i (rbV (i+1) (g * genV i))
  One -> NOne
  Fun (s, ρ) -> NFun (s, rbEnv i ρ)
  Sum (s, ρ) -> NSum (s, rbEnv i ρ)
  Nt l -> NNt (rbN i l)

rbN :: Int -> Neut -> NNeut
rbN i k = case k of
  Gen j -> NGen j
  App k v -> NApp (rbN i k) (rbV i v)
  Fst k -> NFst (rbN i k)
  Snd k -> NSnd (rbN i k)
  NtFun (s, ρ) k -> NNtFun (s, rbEnv i ρ) (rbN i k)

rbEnv :: Int -> Env -> NEnv
rbEnv _ MtEnv = NMtEnv
rbEnv i (UpVar ρ pt v) = NUpVar (rbEnv i ρ) pt (rbV i v)
rbEnv i (UpLet ρ d   ) = NUpLet (rbEnv i ρ) d

-- Error monad

data G a = Success a | Fail Name

instance Functor G where
  fmap f (Success a) = Success (f a)
  fmap f (Fail s) = Fail s

instance Applicative G where
  pure = Success
  (Success f) <*> a = fmap f a
  (Fail s) <*> a = Fail s

instance Monad G where
  (Success x) >>= k = k x
  Fail s      >>= k = Fail s
  return            = Success
  fail              = Fail

type TEnv = [(Name, Val)]

lookupG :: (Show a, Eq a) => a -> [(a, b)] -> G b
lookupG x [] = fail $ "lookupG " ++ show x
lookupG x ((y, u) : us) | x == y = return u
lookupG x ((y, u) : us)          = lookupG x us

-- updating type environment Γ ⊢ p : t = u => Γ'

updateG :: TEnv -> Patt -> Val -> Val -> G TEnv
updateG γ PUnit _ _ = return γ
updateG γ (PVar x) tp _ = return $ (x, tp):γ
updateG γ (PPair p1 p2) (Sig t g) v =
  do γ0 <- updateG γ p1 t (vfst v)
     updateG γ0 p2 (g * vfst v) (vsnd v)
updateG _ p _ _ = fail $ "updateG: p = " ++ show p

checkT :: Int -> Env -> TEnv -> Exp -> G ()
checkT i ρ γ (EPi pt a b) =
  do checkT i ρ γ a
     γ0 <- updateG γ pt (eval a ρ) (genV i)
     checkT (i+1) (UpVar ρ pt (genV i)) γ0 b
checkT i ρ γ (ESig pt a b) = checkT i ρ γ (EPi pt a b)
checkT _ _ _ EUni = return ()
checkT i ρ γ e = check i ρ γ e Set

check :: Int -> Env -> TEnv -> Exp -> Val -> G ()
check i ρ γ e t = case (e, t) of
  (EUnit, One) -> return ()
  (EOne, Set) -> return ()
  (ELam pt e, Pi t g) ->
    do let gen = genV i
       γ0 <- updateG γ pt t gen
       check (i+1) (UpVar ρ pt gen) γ0 e (g * gen)
  (EPair e1 e2, Sig t g) ->
    do check i ρ γ e1 t
       check i ρ γ e2 (g * eval e1 ρ)
  (ECon c e, Sum (cas, ρ0)) ->
    do a <- lookupG c cas
       check i ρ γ e (eval a ρ0)
  (EFun ces, Pi (Sum (cas, ρ0)) g) ->
    if map fst ces == map fst cas
    then sequence_ [ check i ρ γ e (Pi (eval a ρ0) (CloVCompose g c))
                   | ((c, e), (_, a)) <- zip ces cas ]
    else fail "case branches does not match the data type"
  (EPi pt a b, Set) ->
    do check i ρ γ a Set
       let gen = genV i
       γ0 <- updateG γ pt (eval a ρ) gen
       check (i+1) (UpVar ρ pt gen) γ0 b Set
  (ESig pt a b, Set) ->
    check i ρ γ (EPi pt a b) Set
  (ESum cas, Set) ->
    sequence_ [check i ρ γ a Set | (_, a) <- cas]
  (ELet d e, t) ->
    do γ0 <- checkDecl i ρ γ d
       check i (UpLet ρ d) γ0 e t
  (e, t) ->
    do t1 <- checkI i ρ γ e
       eqNf i t t1
  where
    eqNf :: Int -> Val -> Val -> G ()
    eqNf i t1 t2
      | e1 == e2 = return ()
      | otherwise = fail $ "eqNf: " ++ show e1 ++ " ≠ " ++ show e2
      where e1 = rbV i t1
            e2 = rbV i t2

showVal :: Val -> String
showVal u = show (rbV 0 u)

extractPiG :: Val -> G (Val, Clos)
extractPiG (Pi t g) = return (t, g)
extractPiG v = fail $ "cannot extract Π type: " ++ showVal v

extractSigG :: Val -> G (Val, Clos)
extractSigG (Sig t g) = return (t, g)
extractSigG v = fail $ "cannot extract Σ type: " ++ showVal v

checkI :: Int -> Env -> TEnv -> Exp -> G Val
checkI i ρ γ e = case e of
  EVar x -> lookupG x γ
  EApp e1 e2 ->
    do t1 <- checkI i ρ γ e1
       (t, g) <- extractPiG t1
       check i ρ γ e2 t
       return (g * eval e2 ρ)
  EFst e ->
    do t <- checkI i ρ γ e
       (a, _) <- extractSigG t
       return a
  ESnd e ->
    do t <- checkI i ρ γ e
       (_, b) <- extractSigG t
       return (b * vfst (eval e ρ))
  e -> fail $ "checkI: " ++ show e


checkDecl :: Int -> Env -> TEnv -> Decl -> G TEnv
checkDecl i ρ γ (Let pt tp e) = do
  checkT i ρ γ tp
  let t = eval tp ρ
  check i ρ γ e t
  updateG γ pt t (eval e ρ)
checkDecl i ρ γ d@(Letrec pt tp e) = do
  checkT i ρ γ tp
  let t = eval tp ρ
      gen = genV i
  γ0 <- updateG γ pt t gen
  check (i+1) (UpVar ρ pt gen) γ0 e t
  let v = eval e (UpLet ρ d)
  updateG γ pt t v

checkMain :: Exp -> G ()
checkMain e = check 0 MtEnv [] e One
