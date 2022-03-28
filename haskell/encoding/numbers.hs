{-# LANGUAGE RankNTypes #-}

data Nat = Zero
         | Succ Nat

newtype NatChurch = NatChurch (forall r . r -> (r -> r) -> r)

zeroChurch :: NatChurch
zeroChurch = NatChurch const

succChurch :: NatChurch -> NatChurch
succChurch (NatChurch n) = NatChurch (\z s -> s (n z s))

addChurch :: NatChurch -> NatChurch -> NatChurch
addChurch (NatChurch n) (NatChurch m) = NatChurch (\z s -> n (m z s) s)

evalChurch :: NatChurch -> Int
evalChurch (NatChurch n) = n 0 succ

newtype NatScott = NatScott (forall r . r -> (NatScott -> r) -> r)

zeroScott :: NatScott
zeroScott = NatScott const

succScott :: NatScott -> NatScott
succScott n = NatScott (\_ s -> s n)

addScott :: NatScott -> NatScott -> NatScott
addScott n (NatScott m) = m n (succScott . addScott n)

evalScott :: NatScott -> Int
evalScott (NatScott n) = n 0 (succ . evalScott)
