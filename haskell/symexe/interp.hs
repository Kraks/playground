-- From Definitional Interpreters to Symbolic Executor
-- Adrian D. Mensing et al.

{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}

import Data.Maybe
import Control.Monad.Fail as Fail
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader)
import qualified Control.Monad.Reader as Reader

import ListMonad

data Expr = Con String [Expr]
          | Case Expr [(Patt, Expr)]
          | Var String
          | Lam String Expr
          | App Expr Expr
          | Let [(String, Expr)] Expr
          | Letrec [(String, ValExpr)] Expr
          | EEq Expr Expr
          deriving (Show, Eq)

data ValExpr = VCon String [ValExpr]
             | VLam String Expr
          deriving (Show, Eq)

data Patt = PVar String
          | PCon String [Patt]
          deriving (Show, Eq)

type Env val = [(String, val)]

class Monad m => MonadEnv val (m :: * -> *) where
  ask :: m (Env val)
  local :: (Env val -> Env val) -> m val -> m val

class Monad m => MonadBranch cval rval (fork :: (* -> *) -> * -> *) (m :: * -> *) where
  branch :: cval -> fork m rval -> m rval

newtype ITE m a = ITE (m a, m a)

instance Monad m => MonadBranch Bool rval ITE m where
  branch True  (ITE (t, _)) = t
  branch False (ITE (_, e)) = e

class Monad m => MonadMatch val (fork :: (* -> *) -> * -> *) (m :: * -> *) where
  match :: val -> fork m val -> m val

newtype Cases m a = Cases [(Patt, m a)]

class TermVal val where
  con_v :: String -> [val] -> val

class FunVal val where
  clo_v :: String -> Expr -> Env val -> val

class FunApp val m where
  app :: val -> val -> m val

class TermEq val m where
  eq :: val -> val -> m val

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)

class (MonadEnv val m,
       MonadMatch val Cases m,
       TermVal val,
       FunVal val,
       FunApp val m,
       TermEq val m,
       MonadFail m) => EffVal m val where

resolve :: String -> Env v -> v
resolve x nv = fromJust (lookup x nv)

interp :: EffVal m val => Expr -> m val
interp (Con c es) = do
  vs <- mapM interp es
  return (con_v c vs)
interp (Case e bs) =
  let vs = map (mapSnd interp) bs in do
    v <- interp e
    match v (Cases vs)
interp (Var x) = do
  nv <- ask
  return (resolve x nv)
interp (Lam x e) = do
  nv <- ask
  return (clo_v x e nv)
interp (App e1 e2) = do
  f <- interp e1
  v <- interp e2
  app f v
interp (Let xses e) = do
  nv <- mapM interpSnd xses
  local (\nv0 -> nv ++ nv0) (interp e)
  where interpSnd (x, e) = do
          v <- interp e
          return (x, v)
interp (Letrec xsvs e) = do
  nv <- ask
  let nv_b = map (mapSnd (interpval nv_r)) xsvs -- uses lazy evaluation
      nv_r = nv_b ++ nv in
    local (\_ -> nv_r) (interp e)
interp (EEq e_1 e_2) = do
  v_1 <- interp e_1
  v_2 <- interp e_2
  eq v_1 v_2

interpval :: (TermVal val, FunVal val) => Env val -> ValExpr -> val
interpval nv (VLam x e)  = clo_v x e nv
interpval nv (VCon x es) = con_v x (map (interpval nv) es)

data ConcreteValue = ConV String [ConcreteValue]
                   | CloV String Expr (Env ConcreteValue)
  deriving (Show, Eq)

type ConcreteMonad = ReaderT (Env ConcreteValue) (Except String)

instance MonadMatch ConcreteValue Cases ConcreteMonad where
  match v (Cases ((p, m) : bs)) = case vmatch (v, p) of
                                    Just nv -> local (\nv0 -> nv ++ nv0) m
                                    Nothing -> match v (Cases bs)
  match _ (Cases []) = throwError "match failure"

instance TermVal ConcreteValue where
  con_v = ConV

instance FunVal ConcreteValue where
  clo_v = CloV

instance {-# OVERLAPPING #-} Monad m => MonadFail (ExceptT String m) where
  fail s = throwError s

instance (Monad m, MonadReader (Env v) m) => MonadEnv v m where
  ask   = Reader.ask
  local = Reader.local

instance FunApp ConcreteValue ConcreteMonad where
  app (CloV x e nv) v = local (\ _ -> (x, v) : nv) (interp e)
  app _ _ = throwError "Could not apply non-function"

instance TermEq ConcreteValue ConcreteMonad where
  eq v1 v2 | v1 == v2 = return (ConV "true" [])
  eq _  _  = return (ConV "false" [])

instance EffVal ConcreteMonad ConcreteValue where

vmatch :: (ConcreteValue, Patt) -> Maybe (Env ConcreteValue)
vmatch (ConV s vs, PCon s' ps) =
  if (s == s' && length vs == length ps)
  then concat <$> mapM vmatch (zip vs ps)
  else Nothing
vmatch (v, PVar x) = Just [(x, v)]
vmatch _ = Nothing

runSteps :: Expr -> Env ConcreteValue -> Either String ConcreteValue
runSteps e nv = runExcept (runReaderT (interp e) nv)

-- Sec 3. Towards a Symbolic Executor

data Free' f a where
  Pure :: a -> Free' f a
  Free' :: f (Free' f a) -> Free' f a

data Free (c :: * -> *) (a :: *) where
  Stop :: a -> Free c a
  Step :: (c b) -> (b -> Free c a) -> Free c a

instance Functor (Free c) where
  fmap f (Stop a) = Stop (f a)
  fmap f (Step c g) = Step c (\x -> fmap f (g x))

instance Applicative (Free c) where
  pure = Stop
  (<*>) :: Free c (a -> b) -> Free c a -> Free c b
  Stop f <*> Stop a = Stop (f a)
  Stop f <*> Step c g = Step c (\x -> fmap f (g x))
  Step x g <*> f = Step x ((<*> f) <$> g)

instance Monad (Free c) where
  return = Stop
  (>>=) :: Free c a -> (a -> Free c b) -> Free c b
  Stop a >>= k = k a
  Step c f >>= k = Step c (\x -> f x >>= k)

data Cmd (val :: *) (x :: *) where
  Match :: val -> Cases (Free (Cmd val)) val -> Cmd val val
  Local :: (Env val -> Env val) -> Free (Cmd val) val -> Cmd val val
  Ask :: Cmd val (Env val)
  App_c :: val -> val -> Cmd val val
  Eq_c :: val -> val -> Cmd val val
  Fail :: String -> Cmd val a

liftF :: c a -> Free c a
liftF c = Step c Stop

instance MonadFail (Free (Cmd x)) where
  fail s = liftF (Fail s)

instance {-# OVERLAPPING #-} MonadEnv v (Free (Cmd v)) where
  ask = liftF Ask
  local f m = liftF (Local f m)

instance MonadMatch val Cases (Free (Cmd val)) where
  match v (Cases bs) = liftF (Match v (Cases bs))

instance FunApp val (Free (Cmd val)) where
  app f a = liftF (App_c f a)

instance TermEq val (Free (Cmd val)) where
  eq v1 v2 = liftF (Eq_c v1 v2)

instance (TermVal val, FunVal val) => EffVal (Free (Cmd val)) val where

comp :: (TermVal val, FunVal val) => Expr -> Free (Cmd val) val
comp = interp

type Thread_c = Free (Cmd ConcreteValue)

step :: Thread_c ConcreteValue -> ConcreteMonad (Thread_c ConcreteValue)
step (Stop x) = return (Stop x)
step (Step (Match _ (Cases [])) _) =
  throwError "pattern match failure"
step (Step (Match v (Cases ((p, m) : bs))) k) =
  case vmatch (v, p) of
    Just nv -> return (Step (Local (\nv0 -> nv ++ nv0) m) k)
    Nothing -> step (Step (Match v (Cases bs)) k)
step (Step (Local f m) k) = do
  r <- Reader.local f (step m)
  let rt = case r of
        Stop x -> k x
        _ -> Step (Local f r) k
  return rt
step (Step Ask k) = do
  nv <- Reader.ask
  return (k nv)
step (Step (App_c (CloV x e nv) a) k) = do
  return (Step (Local (\_ -> (x, a) : nv) (interp e)) k)
step (Step (App_c _ _) _) =
  throwError "expected a function value or application"
step (Step (Eq_c v1 v2) k) =
  if v1 == v2 then return (k (ConV "true" []))
  else return (k (ConV "false" []))
step (Step (Fail s) _) =
  throwError s

-- Sec 4. From Definitional Interpreter to Symbolic Executor

data SymValue = SConV String [SymValue]
              | SCloV String Expr (Env SymValue)
              | SymV String

type SymMonad = ReaderT (Env SymValue) (StateT Int (Except String))

type Unifier = [(String, SymValue)]
type Unifier_N = [(SymValue, SymValue)]
type SymSetMonad = StateT (Unifier, Unifier_N) (ListT SymMonad)
