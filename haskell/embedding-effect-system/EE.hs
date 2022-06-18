{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators,
             TypeFamilies, MultiParamTypeClasses, FlexibleInstances,
             UndecidableInstances, ScopedTypeVariables, PolyKinds,
             FlexibleContexts, RebindableSyntax
#-}

module EES.Effect where

import Prelude hiding (Monad(..))

-- from type-level-set package
import Data.Type.Map
import Data.Monoid

import GHC.Exts (Constraint)
import GHC.TypeLits

-- Monoid-indexed Monad

class Effect (m :: k -> * -> *) where
  type Unit m :: k
  type Plus m (f :: k) (g :: k) :: k

  type Inv m (f :: k) (g :: k) :: Constraint
  type Inv m f g = ()

  return :: a -> m (Unit m) a

  (>>=) :: (Inv m f g) => m f a -> (a -> m g b) -> m (Plus m f g) b

  (>>) :: (Inv m f g) => m f a -> m g b -> m (Plus m f g) b
  x >> y = x >>= (\_ -> y)

class Subeffect (m :: k -> * -> *) f g where
  sub :: m f a -> m g a

-- Writer Effect

data Writer (w :: [Mapping Symbol *]) a = Writer { runWriter :: (a, Map w) }

instance Effect Writer where
  type Inv Writer s t = (IsMap s, IsMap t, Unionable s t)
  type Unit Writer = '[]
  type Plus Writer s t = Union s t
  return x = Writer (x, Empty)
  (Writer (a, w)) >>= k = let Writer (b, w') = k a
                          in Writer (b, w `union` w')

-- Values of the same type can be combined
type instance Combine v v = v

{-| Define the operation for removing duplicates using mappend -}
instance (Monoid u, Nubable ((k :-> u) ': s)) => Nubable ((k :-> u) ': (k :-> u) ': s) where
  nub (Ext _ u (Ext k v s)) = nub (Ext k (u `mappend` v) s)

instance Semigroup Int where
  (<>) = (+)
instance Monoid Int where
  mappend = (+)
  mempty  = 0

put :: Var v -> a -> Writer '[v :-> a] ()
put v a = Writer ((), Ext v a Empty)

varX = Var :: (Var "x")
varY = Var :: (Var "y")

test :: Writer '["x" :-> Int, "y" :-> [Char]] ()
test = do put varX (42 :: Int)
          put varY "Hello"
          put varX (58 :: Int)
          put varY " World"

-- variable type polymorphic
test' :: (Monoid a, Num a) => a -> Writer '["x" :-> a, "y" :-> [Char]] ()
test' (n :: a) = do
   put varX (42 :: a)
   put varY "hello"
   put varX (n :: a)
   put varY " world"

-- effect polymorphic
test2 :: (IsMap f, Unionable f '["y" :-> String]) =>
         (Int -> Writer f t) ->
         Writer (Union f '["y" :-> String]) ()
test2 f = do { f 3; put varY "world." }

-- Subeffecting

{- Sub effecting for the parametric effect monad -}
instance Supermap s t => Subeffect Writer s t where
  sub (Writer (a, w)) = Writer (a, (supermap w)::(Map t))

{-| Computes supermaps of maps of variable-type mappings, using the 'mempty' operation  -}
class Supermap s t where
  supermap :: Map s -> Map t

instance Supermap '[] '[] where
  supermap Empty = Empty

instance (Monoid x, Supermap '[] s) => Supermap '[] ((k :-> x) ': s) where
  supermap Empty = Ext Var mempty (supermap Empty)

instance Supermap s t => Supermap ((k :-> v) ': s) ((k :-> v) ': t) where
  supermap (Ext k x xs) = Ext k x (supermap xs)
