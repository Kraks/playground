-- Monoid
import Prelude hiding (Monoid, mempty, mappend)

-- a set S, with an associative operator, and an empty element

class Monoid a where
  mempty :: a
  mappend :: a -> a -> a

instance (Monoid a, Monoid b) => Monoid (a, b) where
  mempty = (mempty, mempty)
  mappend (a1, b1) (a2, b2) = (mappend a1 a2, mappend b1 b2)

instance (Monoid a) => Monoid (Maybe a) where
  mempty = Nothing
  mappend Nothing m = m
  mappend m Nothing = m
  mappend (Just m1) (Just m2) = Just (mappend m1 m2)

-- (Bool, &&, True)
newtype All = All { getAll :: Bool }
              deriving (Eq, Ord, Read, Show, Bounded)

instance Monoid All where
  mempty = All True
  All x `mappend` All y = All (x && y)

-- (Bool, ||, False)
newtype Any = Any { getAny :: Bool }
              deriving (Eq, Ord, Read, Show, Bounded)
              
instance Monoid Any where
  mempty = Any False
  Any x `mappend` Any y = Any (x || y)

-- (Z, *, 1)
newtype Product a = Product { getProduct :: a}

instance Num a => Monoid (Product a) where
  mempty = Product 1
  Product x `mappend` Product y = Product (x * y)

-- (Z, +, 0)
newtype Sum a = Sum { getSum :: a }

instance Num a => Monoid (Sum a) where
  mempty = Sum 0
  Sum x `mappend` Sum y = Sum (x + y)

-- list as monoid
instance Monoid [a] where
  mempty = []
  mappend = (++)

-- (f:{a->a}, ., id)
newtype Endo a = Endo { appEndo :: a -> a }

instance Monoid (Endo a) where
  mempty = Endo id
  Endo f `mappend` Endo g = Endo (f . g)

-- (f:{a->a}, >>>, id)
newtype FunApp a = FunApp { appFunApp :: a -> a}
instance Monoid (FunApp a) where
  mempty = FunApp id
  FunApp f `mappend` FunApp g = FunApp (g . f)

