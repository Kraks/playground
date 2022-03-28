-- Chapter 5

factorial :: Integer -> Integer
factorial n = if n < 0 then error "n is less than 0"
              else if n == 0 then 1
              else n * factorial (n-1)

mygcd :: Int -> Int -> Int
mygcd x y = if y == 0 then x else mygcd y (mod x y)

power :: Int -> Int -> Int
power _ 0 = 1
power x n = x * power x (n-1)

power' :: Int -> Int -> Int
power' _ 0 = 1
power' x n | odd n = let p = power x ((n-1) `div` 2) in x * p * p
           | otherwise = let p = power x (n `div` 2) in p * p

product' [] = 1
product' (x:xs) = x * product' xs

cons = (:)

snoc :: a -> [a] -> [a]
snoc x [] = [x]
snoc x (y:ys) = y : snoc x ys

last' :: [a] -> a
last' [] = error "empty list"
last' (x:[]) = x
last' (x:xs) = last' xs

take' n _ | n <= 0 = []
take' _ [] = []
take' n (x:xs) = x : take' (n-1) xs

total' [] n = n
total' (x:xs) n = total' xs $! (x+n) -- force (x+n)

fibStep :: Num a => (a, a) -> (a, a)
fibStep (u, v) = (v, u+v)

fibPair :: (Eq a, Num a) => a -> (a, a)
fibPair 0 = (0, 1)
fibPair n = fibStep (fibPair (n-1))

fastFib :: (Eq a, Num a) => a -> a
fastFib = fst . fibPair

fibs n = map fastFib [1..n]

fibs' n = take n (map fst (iterate fibStep (0, 1)))

golden :: Fractional a => Int -> [a]
golden n = take n (map (\(x, y) -> x/y) (iterate fibStep (0, 1)))

combine :: [(a, a)] -> [(a, a, a)]
combine ((a,b):(c,d):xs) = (a,b,d) : combine ((c,d):xs)
combine _ = []

fibPairs :: Int -> [(Int, Int)]
fibPairs n = map fibPair [1..n]

difference :: Int -> [Int]
difference n = map (\(x,y,z) -> x*z-y*y) (combine $ fibPairs n)

----------------------

search :: (Ord a) => a -> [a] -> Bool
search a [] = False
search a xs | m < a = search a rhs
            | m > a = search a lhs
            | otherwise = True
            where (lhs, m:rhs) = splitAt (length xs `div` 2) xs

-- hanoi
hanoi :: Int -> [(Int, Int)]
hanoi n = move (n, 1, 2, 3)

move :: (Int, Int, Int, Int) -> [(Int, Int)]
move (1, from, to, via) = [(from, to)]
move (n, from, to, via) = move (n-1, from, via, to) ++ [(from, to)] ++ move (n-1, via, to, from)

-- insertion sort
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) | x < y = x:y:ys
                | otherwise = y : insert x ys

insertionSort :: Ord a => [a] -> [a]
insertionSort [] = []
insertionSort (x:xs) = insert x (insertionSort xs)

-- bubble sort
swaps :: Ord a => [a] -> [a]
swaps [] = []
swaps [x] = [x]
swaps (x:x':xs) | x > x' = x' : swaps (x:xs)
                | otherwise = x : swaps (x':xs)

fix :: Eq a => (a -> a) -> a -> a
fix f x = let x' = f x in
          if x == x' then x else fix f x'

bubbleSort :: Ord a => [a] -> [a]
bubbleSort xs = fix swaps xs

bubbleSort' :: Ord a => [a] -> [a]
bubbleSort' xs | swaps xs == xs = xs
               | otherwise = bubbleSort' $ swaps xs

bubbleSort'' :: Ord a => [a] -> [a]
bubbleSort'' [] = []
bubbleSort'' xs = bubbleSort'' initElements ++ [lastElements]
                  where swapped = swaps xs
                        initElements = init swapped
                        lastElements = last swapped

-- selection sort
delete :: Eq a => a -> [a] -> [a]
delete _ [] = []
delete x (y:ys) | x == y = ys
                | otherwise = y : delete x ys

selectionSort :: Ord a => [a] -> [a]
selectionSort [] = []
selectionSort xs = let min = minimum xs
                       xs' = delete min xs
                   in min : selectionSort xs'

-- quick sort
quickSort :: Ord a => [a] -> [a]
quickSort [] = []
quickSort (x:xs) = quickSort less ++ [x] ++ quickSort greater
                   where less = filter (< x) xs
                         greater = filter (>= x) xs

filterSplit :: (a -> Bool) -> [a] -> ([a], [a])
filterSplit _ [] = ([], [])
filterSplit f (x:xs) | f x = ((x:l), r)
                     | otherwise = (l, (x:r))
                     where (l, r) = filterSplit f xs

quickSort' :: Ord a => [a] -> [a]
quickSort' [] = []
quickSort' [x] = [x]
quickSort' (x:xs) = quickSort' l ++ [x] ++ quickSort r
                    where (l, r) = filterSplit (< x) xs

-- merge sort
merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = if x < y then y : merge (x:xs) ys
                               else x : merge xs (y:ys)

mergeSort :: Ord a => [a] -> [a]
mergeSort xs = merge (mergeSort x1) (mergeSort x2)
               where (x1, x2) = halve xs
                     halve xs = (take l xs, drop l xs)
                     l = (length xs) `div` 2

------------------
 
fix' :: (a -> a) -> a
fix' f = f (fix' f)

factorial' :: Int -> Int
factorial' = fix' (\f n -> if n==0 then 1 else n * f (n-1))

-- if x not change, then stop
fix'' :: Eq a => (a -> a) -> a -> a
fix'' f x | x == f x = x
          | otherwise = fix'' f (f x)

------------------

squareroot :: Int -> Double -> Double
squareroot 0 x = x
squareroot n x = (squareroot (n-1) x + x / squareroot (n-1) x) / 2

------------------

ones = 1 : ones

nature = 0 : map (+1) nature

fibs'' = (0:1:zipWith (+) fibs'' (tail fibs''))

{- wrong function
shorter :: [a] -> [a] -> [a]
shoter xs ys | x < y = xs
             | otherwise = ys
             where x = length xs
                   y = length ys
-}

lazyShorter :: [a] -> [a] -> Bool
lazyShorter xs ys = short xs ys
                    where short [] ys = True
                          short xs [] = False
                          short (x:xs) (y:ys) = short xs ys
