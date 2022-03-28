{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Alacarte () where

-- Fixing the expression problem

data Expr f = In (f (Expr f))

data Val e = Val Int
type IntExpr = Expr Val

data Add e = Add e e
type AddExpr = Expr Add

data (f :+: g) e = Inl (f e) | Inr (g e)

addExample :: Expr (Val :+: Add)
addExample = In (Inr (Add (In (Inl (Val 42))) (In (Inl (Val 58)))))

-- Evaluation

instance Functor Val where
  fmap f (Val x) = Val x
instance Functor Add where
  fmap f (Add e1 e2) = Add (f e1) (f e2)
instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl e1) = Inl (fmap f e1)
  fmap f (Inr e2) = Inr (fmap f e2)

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)

class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Val where
  evalAlgebra (Val x) = x

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (Inl x) = evalAlgebra x
  evalAlgebra (Inr y) = evalAlgebra y

eval :: Eval f => Expr f -> Int
eval expr = foldExpr evalAlgebra expr

-- Automating injections

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a

instance Functor f => f :<: f where
  inj = id
instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl
instance {-# OVERLAPPABLE #-} (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj

inject :: (g :<: f) => g (Expr f) -> Expr f
inject = In . inj

val :: (Val :<: f) => Int -> Expr f
val x = inject (Val x)

infixl 6 ⊕
(⊕) :: (Add :<: f) => Expr f -> Expr f -> Expr f
x ⊕ y = inject (Add x y)

x :: Expr (Add :+: Val)
x = val 300 ⊕ val 100 ⊕ val 1

-- Examples

data Mul x = Mul x x
instance Functor Mul where
  fmap f (Mul x y) = Mul (f x) (f y)

instance Eval Mul where
  evalAlgebra (Mul x y) = x * y

infixl 7 ⊗
(⊗) :: (Mul :<: f) => Expr f -> Expr f -> Expr f
x ⊗ y = inject (Mul x y)

y :: Expr (Val :+: (Add :+: Mul))
y = val 80 ⊗ val 5 ⊕ val 4

class Render f where
  render :: Render g => f (Expr g) -> String

pretty :: Render f => Expr f -> String
pretty (In t) = render t

instance Render Val where
  render (Val i) = show i
instance Render Add where
  render (Add x y) = "(" ++ pretty x ++ " + " ++ pretty y ++ ")"
instance Render Mul where
  render (Mul x y) = "(" ++ pretty x ++ " * " ++ pretty y ++ ")"
instance (Render f, Render g) => Render (f :+: g) where
  render (Inl x) = render x
  render (Inr y) = render y

-- Monads for free

data Term f a =
    Pure a
  | Impure (f (Term f a))

instance Functor f => Functor (Term f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Impure t) = Impure (fmap (fmap f) t)

instance Functor f => Applicative (Term f) where
  pure = Pure
  -- (<*>) :: Term f (a -> b) -> Term f a -> Term f b
  (Pure f) <*> a = fmap f a
  (Impure f) <*> a = Impure (fmap (<*> a) f)

instance Functor f => Monad (Term f) where
  return x = Pure x
  (Pure x) >>= f = f x
  (Impure t) >>= f = Impure (fmap (>>= f) t)

data Zero a -- Term Zero == identity monad
data One a = One -- Term One = maybe monad
data Const e a = Const e -- Term (Const e) = error monad

data Incr t = Incr Int t
data Recall t = Recall (Int -> t)

instance Functor Recall where
  fmap f (Recall g) = Recall (f . g)
instance Functor Incr where
  fmap f (Incr i t) = Incr i (f t)

inject' :: (g :<: f) => g (Term f a) -> Term f a
inject' = Impure . inj

incr :: (Incr :<: f) => Int -> Term f ()
incr i = inject' (Incr i (Pure ()))

recall :: (Recall :<: f) => Term f Int
recall = inject' (Recall Pure)

tick :: Term (Recall :+: Incr) Int
tick = do y <- recall
          incr 1
          return y

foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Term f a -> b
foldTerm pure imp (Pure x) = pure x
foldTerm pure imp (Impure t) = imp (fmap (foldTerm pure imp) t)

newtype Mem = Mem Int deriving Show

class Functor f => Run f where
  runAlgebra :: f (Mem -> (a, Mem)) -> Mem -> (a, Mem)

instance Run Incr where
  runAlgebra (Incr k r) (Mem i) = r (Mem (i + k))
instance Run Recall where
  runAlgebra (Recall r) (Mem i) = r i (Mem i)
instance (Run f, Run g) => Run (f :+: g) where
  runAlgebra (Inl r) = runAlgebra r
  runAlgebra (Inr r) = runAlgebra r

run :: Run f => Term f a -> Mem -> (a, Mem)
run = foldTerm (,) runAlgebra
