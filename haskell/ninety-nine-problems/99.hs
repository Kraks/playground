import Prelude hiding (last)

import System.Random hiding (split)
import Control.Monad (replicateM)
import Data.List (permutations, tails, subsequences)

-- 1. Find the last element of a list
last :: [a] -> a
last (x:[]) = x
last (_:xs) = last xs
last _ = error "empty list"

-- 2. Find the last but one element of a list
butLast :: [a] -> a
butLast (x:(_:[])) = x
butLast (_:xs) = butLast xs
butLast _ = error "at least two elements"

-- 3. Find the K'th element of a list. The first element in the list is number 1
elementAt :: [a] -> Int -> a
elementAt (x:xs) 1 = x
elementAt (_:xs) n = elementAt xs (n-1)

-- 4. Find the number of elements of a list
myLength :: [a] -> Integer
myLength = foldr (\x acc -> acc+1) 0

myLength' :: [a] -> Integer
myLength' = foldr (const (+1)) 0

-- 5. Reverse a list
myReverse :: [a] -> [a]
myReverse = foldl (flip (:)) []

-- 6. Find out whether a list is a palindrome.
-- A palindrome can be read forward or bacward. e.g. (x a m a x)
isPalindrome :: (Eq a) => [a] -> Bool
isPalindrome []  = True
isPalindrome [x] = True
isPalindrome xs  = (head xs == last xs) && (isPalindrome $ init $ tail xs)

-- 7. Flatten a nested list structure.
data NestedList a = Elem a | List [NestedList a]

flatten :: NestedList a -> [a]
flatten (Elem x) = [x]
flatten (List []) = []
flatten (List (x:xs)) = flatten x  ++ flatten (List xs)

-- 8. Eliminate consecutive duplicates of list elements.
compress :: Eq a => [a] -> [a]
compress [] = []
compress [x] = [x]
compress (x:x':xs) = if x == x' then compress (x':xs) else x:(compress (x':xs))

-- 9. Pack consecutive duplicates of list elements into sublists. 
-- If a list contains repeated elements they should be placed in separate sublists.
pack :: Eq a => [a] -> [[a]]
pack xs = reverse $ auxPack [] xs []

auxPack :: Eq a => [a] -> [a] -> [[a]] -> [[a]]
auxPack acc [] res = acc:res
auxPack [] (y:ys) res = auxPack [y] ys res
auxPack (x:xs) (y:ys) res = if x == y then auxPack (y:x:xs) ys res
                                      else auxPack [] (y:ys) ((x:xs):res)

-- 10. Run-length encoding of a list. 
-- Use the result of problem P09 to implement the so-called run-length 
-- encoding data compression method. Consecutive duplicates of elements 
-- are encoded as lists (N E) where N is the number of duplicates of 
-- the element E.

encode :: Eq a => [a] -> [(Int, a)]
encode xs = auxEncode $ pack xs

auxEncode :: [[a]] -> [(Int, a)] 
auxEncode [] = []
auxEncode (xs:rest) = (length xs, head xs):(auxEncode rest)

-- 11. dified run-length encoding.
-- dify the result of problem 10 in such a way that if an element has 
-- no duplicates it is simply copied into the result list. 
-- Only elements with duplicates are transferred as (N E) lists.
data ListItem a = Single a | Multiple Int a deriving Show
encodeModified :: Eq a => [a] -> [ListItem a]
encodeModified = map transform . encode
  where transform (1, x) = Single x
        transform (n, x) = Multiple n x

-- 12. Decode a run-length encoded list.
-- Given a run-length code list generated as specified in problem 11. Construct its uncompressed version.
decodeModified :: [ListItem a] -> [a]
decodeModified [] = []
decodeModified (Single x:rest) = x:(decodeModified rest)
decodeModified (Multiple n x:rest) = (take n $ repeat x)++(decodeModified rest)

decodeModified' :: [ListItem a] -> [a]
decodeModified' = concatMap transform
  where transform (Single x) = [x]
        transform (Multiple n x) = take n $ repeat x

-- 13. Run-length encoding of a list (direct solution).
-- Implement the so-called run-length encoding data compression method 
-- directly. I.e. don't explicitly create the sublists containing the 
-- duplicates, as in problem 9, but only count them. As in problem P11, 
-- simplify the result list by replacing the singleton lists (1 X) by X.
encodeDirect :: Eq a => [a] -> [ListItem a]
encodeDirect = foldr (\x acc -> 
  case acc of [] -> [Single x]
              (Single x'):rest -> if x == x' then (Multiple 2 x):rest else (Single x):acc
              (Multiple n x'):rest -> if x == x' then (Multiple (n+1) x):rest else (Single x):acc) []

-- 14. Duplicate the elements of a list.
dupli :: Eq a => [a] -> [a]
dupli [] = []
dupli (x:xs) = x:x:(dupli xs)

-- 15. Replicate the elements of a list a given number of times.
repli :: Eq a => [a] -> Int -> [a]
repli [] _ = []
repli (x:xs) n = (take n $ repeat x) ++ (repli xs n)

-- 16. Drop every N'th element from a list.
dropEvery :: Eq a => [a] -> Int -> [a]
dropEvery xs n = aux xs (n-1)
  where aux [] _ = []
        aux (x:xs) i = if i == 0 then aux xs (n-1) else x:(aux xs (i-1))

-- 17. Split a list into two parts, the length of the first part is given.
-- Do not use any predefined predicates.
split :: [a] -> Int -> ([a], [a])
split [] _ = ([], [])
split xs 0 = ([], xs)
split (x:xs) n = (x:(fst rest), snd rest)
  where rest = split xs (n-1)

-- 18. Extract a slice from a list.
-- Given two indices, i and k, the slice is the list containing the 
-- elements between the i'th and k'th element of the original list 
-- (both limits included). Start counting the elements with 1.
slice :: [a] -> Int -> Int -> [a]
slice [] _ _ = []
slice xs 1 m = take m xs
slice (x:xs) n m = slice xs (n-1) (m-1)

-- 19. Rotate a list N places to the left.
rotate :: [a] -> Int -> [a]
rotate xs n 
  | n == 0 = xs
  | n > 0 = (drop n xs) ++ (take n xs)
  | otherwise = rotate xs n'
  where n' = (length xs) - (-n)

-- 20. Remove the K'th element from a list. The index starts from 1.
removeAt :: Eq a => Int -> [a] -> (a, [a])
removeAt _ [] = error "empty list"
removeAt 1 (x:xs) = (x, xs)
removeAt n (x:xs) = (fst res, x:(snd res))
  where res = removeAt (n-1) xs

-- 21. Insert an element at a given position into a list.
insertAt :: a -> [a] -> Int -> [a]
insertAt y xs 1 = y:xs
insertAt y (x':xs) n = x':(insertAt y xs (n-1))

-- 22. Create a list containing all integers within a given range.
range :: Int -> Int -> [Int]
range s e 
  | s == e = [s]
  | otherwise = s:(range (s+1) e)

-- 23. Extract a given number of randomly selected elements from a list.
rndSelect :: [a] -> Int -> IO [a]
rndSelect [] _ = return []
rndSelect xs n 
  | n < 0 = error "N should be greater than zero"
  | otherwise = do pos <- replicateM n $ getStdRandom $ randomR (0, (length xs)-1)
                   return [xs !! p | p <- pos]

rndSelect' :: [a] -> Int -> IO [a]
rndSelect' [] _ = return []
rndSelect' xs n 
  | n < 0 = error "N should be greater than zero"
  | otherwise = replicateM n rand
    where rand = do r <- randomRIO (0, (length xs)-1)
                    return (xs !! r)

-- 24. Draw N different random numbers from set 1 .. M.
diffSelect :: Int -> Int -> IO [Int]
diffSelect n u = do ns <- replicateM n $ getStdRandom $ randomR (0, u) 
                    return ns

-- 25. Generate a random permutation of the elements of a list.
rndPermu :: [a] -> IO [a]
rndPermu [] = return []
rndPermu (x:xs) = do rand <- randomRIO (0, length xs)
                     rest <- rndPermu xs
                     return $ let (ys, zs) = splitAt rand rest
                               in ys ++ (x:zs)

rndElem :: [a] -> IO a
rndElem xs = do idx <- randomRIO (0, length xs - 1)
                return (xs !! idx)

rndPermu' :: [a] -> IO [a]
rndPermu' xs = rndElem . permutations $ xs

-- 26. Generate the conbinations of K distinct objects chosen from the N elements of a list.
combinations :: Int -> [a] -> [[a]]
combinations k ns = filter ((k==).length) (subsequences ns)

combinations' :: Int -> [a] -> [[a]]
combinations' 0 _ = [[]]
combinations' n xs = [xs !! i : x | i <- [0..(length xs)-1],
                                    x <- combinations' (n-1) (drop (i+1) xs)]

-- 27.  
