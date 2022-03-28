-- Chapter 3
import Prelude hiding ((/=), (==), not, and, or, (&&), (||))


(==) :: Bool -> Bool -> Bool
(==) True True = True
(==) False False = True
(==) _ _ = False

not :: Bool -> Bool
not True = False
not False = True

not' :: Bool -> Bool
not' = (== False)

xor, and, or :: Bool -> Bool -> Bool
xor b1 b2 = not $ b1 == b2

and True b1 = b1
and False _ = False

or False b1 = b1
or True _ = True

cond :: Bool -> a -> a -> a
cond True thn els = thn
cond False thn els = els

infix 4 == 
infix 4 /=
infixl 3 &&
infixl 2 ||

(||) = or
(&&) = and
(/=) = xor

-- if a and b are both 1, then S is 0, C is 1
-- if a or b is 1, then S is 1, C is 0
hAdd :: Bool -> Bool -> (Bool, Bool)
hAdd a b = (a /= b, a && b)

fAdd :: Bool -> Bool -> Bool -> (Bool, Bool)
fAdd a b c = let (axb, aab) = hAdd a b in
             let (axbxc, axbac) = hAdd axb c in
             (axbxc, aab || axbac)

nand, nor :: Bool -> Bool -> Bool
nand True True = False
nand _ _ = True

nor False False = True
nor _ _ = False

not1, not2 :: Bool -> Bool
not1 b = nand b b
not2 b = nor b b

and1, and2 :: Bool -> Bool -> Bool
-- and1 b1 b2 = not1 (nand b1 b2)
and1 b1 b2 = nand (nand b1 b2) (nand b1 b2)
-- and2 b1 b2 = nor (not2 b1) (not2 b2)
and2 b1 b2 = nor (nor b1 b1) (nor b2 b2)

or1, or2 :: Bool -> Bool -> Bool
-- or1 b1 b2 = nand (not1 b1) (not1 b2)
or1 b1 b2 = nand (nand b1 b1) (nand b2 b2)
-- or2 b1 b2 = not2 $ nor b1 b2
or2 b1 b2 = nor (nor b1 b2) (nor b1 b2)
