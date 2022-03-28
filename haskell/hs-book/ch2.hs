import Data.List

-- Chapter 2

{- Data Type 
    Bool
    Char
    Int, depends on OS
    Word, depends on OS
    Integer
    String, [Char]
    Tuple, fst, snd
    List
-}

uncurry_plus = uncurry (+)

-- Type synonym
type RGB = (Int, Int, Int)
type Picture = [[RGB]]

{- Type Class
    Eq
    Ord
    Enum
    Bounded
    Num
    Show
-}

add, sub :: Int -> Int -> Int
add a b = a + b
sub a b = a - b

f :: Num a => a -> a
f x = 4 *x + 1

area r = pi * r ^ 2

f' :: Num a => (a, a) -> a
f' (x, y) = 4 * x + 5 * y + 1

g = \x -> \y -> x y
three = g (+) 1 2

-- Monomporphism restriction
-- may add {-# LANGUAGE NoMonomorphismRestriction #-} to head of file
two_len xs = let len = genericLength xs in (len, len)
h = (+)
h' :: Num a => a -> a -> a
h' = (+)

s :: Double -> Double -> Double -> Double
s a b c = let p = (a+b+c)/2 in sqrt (p*(p-a)*(p-b)*(p-c))

six = let f x = x + 1 in f 5

four = let x = 2; y = 2 in x + y

s' :: Double -> Double -> Double -> Double
s' a b c = sqrt (p*(p-a)*(p-b)*(p-c))
            where p = (a+b+c)/2

month :: Int -> Int
month n = case n of
            1 -> 31
            2 -> 28
            _ -> error "March or later"

abs' :: (Num a, Ord a) => a -> a
abs' n | n > 0 = n
       | otherwise = -n

-- (^) :: (Num a, Integral b) => a -> b -> a
-- (^^) :: (Integral b, Fractional a) => a -> b -> a
-- (**) :: Floating a => a -> a -> a

-- div, mod
-- quot, rem

-- application is left associative
-- type annotation is right associative

-- infixl
-- infixr
-- infix
