{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.String

data I a = I { unI :: a }
data Var a x = Var { unK :: a}

infixr 8 +
data (f + g) a = InL (f a) | InR (g a)

class sub :<: sup where
  inj :: sub a -> sup a

instance {-# OVERLAPPING #-} (sym :<: sym) where
  inj = id

instance {-# OVERLAPPING #-} (sym1 :<: (sym1 + sym2)) where
  inj = InL

instance {-# OVERLAPPING #-} (sym1 :<: sym3) => (sym1 :<: (sym2 + sym3)) where
  inj = InR . inj

instance {-# OVERLAPPING #-} (I :<: g, IsString s) => IsString ((f + g) s) where
  fromString = inj . I . fromString

var :: (Var a :<: f) => a -> f e
var = inj . Var

elim :: (I :<: f) => (a -> b) -> (Var a + f) b -> f b
elim eval f = case f of
                InL (Var xs) -> inj (I (eval xs))
                InR g        -> g

data UserVar = UserName
data XMasVar = XMasPresent

email :: [(Var UserVar + Var XMasVar + I) String]
email = [ "Dear "
        , var UserName
        , ", thank you ..."
        , "You have asked for a: "
        , var XMasPresent
        ]

main :: IO ()
main = do name <- getLine
          present <- getLine
          putStrLn (concatMap (unI .
                                (elim (\c -> present) .
                                 elim (\u -> name)))
                              email)
