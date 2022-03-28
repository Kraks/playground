-- Ch9, Fixed length list

{-# LANGUAGE GADTs, MultiParamTypeClasses, TypeFamilies, FlexibleInstances #-}

data O = VO
data S n = VS n

data FList n t where
  FNil :: FList O t
  FCons :: t -> FList n t -> FList (S n) t

abc = (FCons 'a' (FCons 'b' (FCons 'c' FNil)))

class FIndex m n where
  fIndex :: m -> FList n t -> t

instance FIndex O (S n) where
  fIndex VO (FCons x _) = x

-- why FIndex m n ?
instance FIndex m n => FIndex (S m) (S n) where
  fIndex (VS m) (FCons _ xs) = fIndex m xs

fHead :: FList (S n) t -> t
fHead (FCons x _) = x

fTail :: FList (S n) t -> FList n t
fTail (FCons _ xs) = xs

class FAppend m n where
  type Sum m n :: *
  fAppend :: FList m t -> FList n t -> FList (Sum m n) t

instance FAppend O n where
  type Sum O n = n
  fAppend FNil ys = ys

instance FAppend m n => FAppend (S m) n where
  type Sum (S m) n = S (Sum m n)
  fAppend (FCons x xs) ys = FCons x (fAppend xs ys)

-- some tests
four = fIndex (VS (VS (VS VO)))
         (fAppend (FCons 1 (FCons 2 FNil))
                  (FCons 3 (FCons 4 FNil)))
