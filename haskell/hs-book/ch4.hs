-- Chapter 4
import Data.Char
import Data.Bits

five = id 5

t = id True

t' = const True 3

second :: b -> a -> a
second = const id

six = flip (-) 2 8

second' = flip const

month :: Int -> Int
month = undefined

-- List

t'' = null []

four = length [1, 2, 3, 4]

avg xs = sum xs / fromIntegral $ length xs

-- genericLength :: Num a => [b] -> a

-- !!
-- reverse
-- head, last
-- init, tail
-- map, filter
-- take, drop
-- span, break
-- takeWhile, dropWhile

takeWhile' :: (a -> Bool) -> [a] -> [a]
takeWhile' = curry (fst . uncurry span)

dropWhile' :: (a -> Bool) -> [a] -> [a]
dropWhile' = curry (snd . uncurry span)

ts = repeat True

five_t = replicate 5 True

replicate' :: Int -> a -> [a]
replicate' n a = take n (repeat a)

-- any even [1, 2, 3, 4] => True
-- all odd [1, 3, 4] => True

has_one = elem 1 [1, 2, 3]

elem' :: Eq a => a -> [a] -> Bool
elem' x xs = not $ null (filter (== x) xs)

elem'' :: Eq a => a -> [a] -> Bool
elem'' a [] = False
elem'' a (x:xs) = if a == x then True else elem'' a xs

exp_of_2 = iterate (*2) 1

five_two_one = until (>500) (*2) 1

a_tuple = zip [1, 2, 3] [4, 5, 6]

another_tuple = zipWith (+) [1, 2, 3] [4, 5, 6]

a_list = concat [[1, 2], [3, 4], [5, 6]]

three_times = concatMap (replicate 3) [1, 2, 3]

---------------

type Weekday = Int
type Year = Int
type Month = Int
type Day = Int

week' :: Year -> Day -> Weekday
week' y d = let y1 = y - 1 in
            (y1 + (div y1 4) - (div y1 100) + (div y1 400) + d) `mod` 7

isLeapYear :: Year -> Bool
isLeapYear y = (mod y 4 == 0) && (mod y 100 /= 0) || (mod y 400 == 0)

monthDays :: Year -> Month -> Int
monthDays y m | m == 2 = if not $ isLeapYear y then 28 else 29
              | elem m [1, 3, 5, 7, 8, 10, 12] = 31
              | elem m [4, 6, 9, 11] = 30
              | otherwise = error "invalid month"

accDays :: Year -> Month -> Day -> Int
accDays y m d | d > monthDays y m = error "invalid days of this month"
              | otherwise = (sum $ take (m-1) (map (monthDays y) [1..12])) + d

week y m d = week' y (accDays y m d)

-- String

-- show :: Show a => a -> String
contain6 = filter (elem '6') (map show [1..100])

-- read :: Read a => String -> a
contain6' = map (\str -> read str :: Int) $ filter (elem '6') (map show [1..100])

-- lines :: String -> [String]
-- unlines :: [String] -> String
two_lines = lines "first line\nsecond line"
a_str = unlines ["first line", "second line"]

-- word :: String -> [String]
-- unword :: [String] -> String
two_words = words "hello world"

reverseSentence :: String -> String
reverseSentence = unwords . reverse . words
--reverseSentence str = unwords (reverse (words str))

