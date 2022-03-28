-- Chapter 6
import Data.Ord (comparing)
import Data.Char (ord, chr, isLower)
import Data.List (delete, tails, minimumBy)

sqrs = [x^2 | x <- [0..100], x < 10]

a_tuple = [(x, y) | x <- [1..4], y <- [1..4]]

map' f xs = [f x | x <- xs]

filter' f xs = [x | x <- xs, f x]

evens = [x | x <- [0..], even x, x > 10]

length' xs = sum [1 | _ <- xs]

a_table = [show x ++ "*" ++ show y ++ "=" ++ show (x*y) | y <- [1..9], x <- [1..y]]

series :: Int -> [Double]
series n = [1 / (2 * (fromIntegral k) +1) * (-1)^k | k <- [0..n]]

pi' = 4 * (sum $ series 200000)

------

factors :: Integral a => a -> [a]
factors n = [x | x <- [1..n], mod n x == 0]

isPrime :: Integral a => a -> Bool
isPrime n = factors n == [1, n]

primes :: Integral a => a -> [a]
primes n = [x | x <- [1..n] , isPrime x]

sieve :: Integral a => [a] -> [a]
sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

primes' = sieve [2..]

------

char2int :: Char -> Int
char2int c = ord c - ord 'a'

int2char :: Int -> Char
int2char n = chr (ord 'a' + n)

shift :: Int -> Char -> Char
shift n c | isLower c = int2char ((char2int c + n) `mod` 26)
          | otherwise = c

encode :: Int -> String -> String
encode n xs = [shift n x | x <- xs]

chisqr :: [Float] -> [Float] -> Float
chisqr os es = sum [((o - e) ^ 2) / e | (o, e) <- zip os es]

table :: [Float]
table = [8.2, 1.5, 2.8, 4.3, 12.7, 2.2, 2.0, 6.1, 7.0, 0.2, 0.8, 4.0, 2.4, 6.7, 7.5, 1.9, 0.1, 6.0, 6.3, 9.1, 2.8, 1.0, 2.4, 0.2, 2.0, 0.1]

count :: Char -> String -> Int
count x xs = length [x' | x' <- xs, x == x']

percent :: Int -> Int -> Float
percent n m = (fromIntegral n / fromIntegral m) * 100

lowers :: String -> Int
lowers xs = length [x | x <- xs, isLower x]

freqs :: String -> [Float]
freqs xs = [percent (count x xs) n | x <- ['a'..'z']]
           where n = lowers xs

rotate :: Int -> [a] -> [a]
rotate n xs = drop n xs ++ take n xs

crack :: String -> String
crack xs = encode (-factor) xs
           where factor = head (positions (minimum chitab) chitab)
                 chitab = [chisqr (rotate n table') table | n <- [0..25]]
                 table' = freqs xs

positions :: Eq a => a -> [a] -> [Int]
positions x xs = [i | (x', i) <- zip xs [0..], x == x']

--------

insert :: a -> [a] -> [[a]]
insert n [] = [[n]]
insert n (n':ns) = (n:n':ns) : [n':ns' | ns' <- insert n ns]

permutation :: Eq a => [a] -> [[a]]
permutation [] = [[]]
permutation (x:xs) = concat [insert x permuxs | permuxs <- permutation xs]

permutation' :: Eq a => [a] -> [[a]]
permutation' [] = [[]]
permutation' xs = [y:ys | y <- xs, ys <- permutation (delete y xs)]

derangements :: [Int] -> [[Int]]
derangements [] = [[]]
derangements l = [x:xs | x <- l, xs <-derangements (delete x l), x /= length l]

derangements' n = map reverse (derangements [1..n])

-------

choice :: (a -> [Bool]) -> [a] -> [[a]]
choice _ [] = [[]]
choice f (x:xs) = [if choose then x:ys else ys | choose <- f x, ys <- choice f xs]

powerSet = choice (\x -> [True, False])

powerSet' :: [a] -> [[a]]
powerSet' [] = [[]]
pwoerSet' (x:xs) = [x:r | r <- powerSet' xs] ++ powerSet' xs

ts = Data.List.tails [1,2,3,4]

combinations :: Int -> [a] -> [[a]]
combinations 0 [] = [[]]
combinations n xs = [y:ys | y:xs' <- tails xs, ys <- combinations (n-1) xs']

-- matrix multiplication

transpose :: [[a]] -> [[a]]
transpose [] = []
transpose ([]:xs) = transpose xs
transpose ((x:xs):xs') = (x : [h | (h:_) <- xs']) : transpose (xs : [t | (_:t) <- xs'])

infixl 5 |*|

(|*|) :: Num a => [[a]] -> [[a]] -> [[a]]
(|*|) a b = [[sum $ zipWith (*) ar bc | bc <- transpose b] | ar <- a]

-- fib

unit = [[1, 1], [1, 0]]

fib 1 = unit
fib n | even n = let m = fib (div n 2) in m |*| m
      | otherwise = let m = fib (div (n-1) 2) in m |*| unit |*| m

-- shortest path
-- CLRS Ch25

type Distance = Double
type Name = String
type Direction = String
type Weight = (Distance, Direction)
type RouteMap = [[Weight]]

infinity :: Fractional a => a
infinity = 1 / 0
i = infinity

zipD :: [Name] -> [[String]]
zipD ns = [[(start ++ "->" ++ des) | des <- ns] | start <- ns]

zipW :: [[Distance]] -> [Name] -> [[Weight]]
zipW ds ns = [zip d n | (d, n) <- zip ds (zipD ns)]

tuplePlus :: Weight -> Weight -> Weight
tuplePlus (d1, n1) (d2, n2) = (d1 + d2, n1 ++ destination)
                              where (from, destination) = break (== '-') n2

step :: RouteMap -> RouteMap -> RouteMap
step a b = [[minimumBy (comparing fst) $ zipWith tuplePlus ar bc | bc <- transpose b] | ar <- a]

iteration :: Int -> (a -> a) -> a -> a
iteration 0 f x = x
iteration n f x = iteration (n-1) f (f x)

steps :: Int -> RouteMap -> RouteMap
steps n route = iteration n (step route) route

fix f x = if dss == dss' then x else fix f x'
          where x' = f x
                dss = [fst $ unzip ds | ds <- x']
                dss' = [fst $ unzip ds | ds <- x]

path :: [[Distance]] -> [Name] -> RouteMap
path dis ns = fix (step route) route
              where route = zipW dis ns

graph :: [[Distance]]
graph = [[0, 6, 2, i, 7],
         [6, 0, 3, i, i],
         [2, 3, 0, 1, 5],
         [i, i, 1, 0, 4],
         [7, i, 5, 4, 0]]

names = ["a", "b", "c", "d", "e"]

res = path graph names
