{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.TypeLits
import Data.Proxy

-- Literals

-- :set -XDataKinds
-- :kind 'True
-- :kind 1

-- Type-level function

type family If c t e where
  If 'True  t e = t
  If 'False t e = e

-- :kind! If 'True Bool Char
-- :kind! If 'False Int Double

-- Type-level list

-- (:) is kind-polymorphic
-- :kind (:)

-- :kind [True, False]
-- :kind [1,2]

-- Type-level list function

type family Length xs where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

-- :kind! Length [Char, Bool, Int]

type family Head (xs :: [*]) where
  Head (x ': xs) = x

-- :kind! Head [Char, Bool, Int]

type family Tail (xs :: [*]) where
  Tail (x ': xs) = xs

-- :kind! Tail [Char, Bool, Int]

type family Map (f :: * -> *) (xs :: [*]) where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

type family MakePair (x :: *) where
  MakePair x = (x, x)

-- :kind! Map MakePair [Char, Bool, Int]

