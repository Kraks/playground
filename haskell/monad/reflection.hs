{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}

import Control.Applicative
import Control.Monad (liftM, ap)
import Data.Dynamic
import Unsafe.Coerce

-- Part I: implementing Output monad

newtype Output a = O { r0 :: (a, String) }

instance Functor Output where
  fmap = liftM

instance Applicative Output where
  pure = return
  (<*>) = ap
  
instance Monad Output where
  return a = O (a, "")
  m >>= f = let (a, s) = r0 m in
                let (b, s') = r0 (f a) in
                    O (b, s ++ s')

out :: Char -> Output ()
out c = O ((), [c])

collect :: Output () -> String
collect m = snd (r0 m)

---------------------------------------

-- String-state monad
newtype Output' a = O' { r0' :: String -> (a, String) }

instance Functor Output' where
  fmap = liftM

instance Applicative Output' where
  pure = return
  (<*>) = ap

instance Monad Output' where
  return a = O' (\s -> (a, s))
  m >>= f = O' (\s -> let (a, s') = r0' m s in r0' (f a) s')

out' :: Char -> Output' ()
out' c = O' (\s -> ((), c : s))

collect' :: Output' () -> String
collect' m = let ((), s) = r0' m [] in reverse s

flush :: Output' ()
flush = O' (\s -> ((), ""))

peek :: Output' Char
peek = O' (\s -> (head s, s))

-------------------------------------
-- Now think of Output as values, Output' as behaviors.

reflectO :: Output a -> Output' a
reflectO m = let (a, s) = r0 m in
                 O' (\s' -> (a, (reverse s) ++ s'))

reifyO :: Output' a -> Output a
reifyO m' = O (let (a, s) = r0' m' [] in (a, reverse s))

-- Now out' can be defined as
out'' c = (reflectO . O) ((), [c])
-- can collect' can be defined as
collect'' m' = snd ((r0 . reifyO) m')

-- reifyO (reflectO m) = m holds, but
-- reflectO (reifyO m') =/= m'

-- Part II. implementing monads with continuations

newtype Cont r a = C { rC :: (a -> r) -> r }

instance Functor (Cont r) where
  fmap = liftM

instance Applicative (Cont r) where
  pure = return
  (<*>) = ap

instance Monad (Cont r) where
  return a = C (\k -> k a)
  m >>= f = C (\k -> rC m (\a -> rC (f a) k))

class Monad m => PCRMonad m where
  pcreflect :: m a -> Cont (m d) a
  pcreify :: (forall d . Cont (m d) a) -> m a
  
  pcreflect m = C (\k -> m >>= k)
  pcreify t = rC t return

-- 

fmDyn :: Typeable a => Dynamic -> a
fmDyn d = fromDyn d (error "Dynamic")

class Monad m => CRmonad m where
  creflect :: m a -> Cont (m Dynamic) a
  creify :: Typeable a => Cont (m Dynamic) a -> m a
  
  creflect m = C (\k -> m >>= k)
  creify t = rC (unsafeCoerce t :: Cont (m a) a) return

