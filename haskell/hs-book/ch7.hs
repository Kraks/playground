import Prelude hiding (foldl1, foldr1, (.), (>>), all, any)

foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' f v [] = v
foldr' f v (x:xs) = f x (foldr' f v xs)

(+++) :: [a] -> [a] -> [a]
(+++) = foldr (:)

insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) | x < y = x:y:ys
                | otherwise = y:insert x ys

insertionSort :: Ord a => [a] -> [a]
insertionSort xs = foldr insert [] xs

skip :: Eq a => a -> [a] -> [a]
skip x [] = [x]
skip x (y:ys) = if x == y then y:ys else x:y:ys

compress :: Eq a => [a] -> [a]
compress = foldr skip []

snoc :: a -> [a] -> [a]
snoc x = foldr (:) [x]

concat :: [[a]] -> [a]
concat = foldr (++) []

map' :: (a -> b) -> [a] -> [b]
map' f = foldr (\l ls -> f l : ls) []

foldl' :: (a -> b -> a) -> a -> [b] -> a
foldl' f v [] = v
foldl' f v (x:xs) = foldl f (f v x) xs

-- Data.List.foldl' is strict

reverse' :: [a] -> [a]
reverse' = foldl (flip (:)) []

-- foldl1, foldr1, should have at least one element in the list
-- strict version: foldl1', foldr1'
foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 _ [x] = x
foldr1 f (x:xs) = f x (foldr1 f xs)
foldr1 _ _ = error "foldr1 empty list"

foldl1 :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs) = foldl f x xs
foldl1 _ [] = error "foldl1 empty list"

unword :: [String] -> String
unword [] = ""
unword ws = foldr1 (\w s -> w ++ ' ':s) ws

maximum', minimum' :: Ord a => [a] -> a
maximum' = foldl1 max
minimum' = foldl1 min

mapAccumL :: (acc -> x -> (acc, y)) -> acc -> [x] -> (acc, [y])
mapAccumL _ s [] = (s, [])
mapAccumL f s (x:xs) = (s'', y:ys)
                       where (s', y) = f s x
                             (s'', ys) = mapAccumL f s' xs

nineteen = mapAccumL (\sum -> \a -> (sum+a, even (sum+a))) 0 [1, 3, 4, 5, 6]

mapAccumR :: (acc -> x -> (acc, y)) -> acc -> [x] -> (acc, [y])
mapAccumR _ s [] = (s, [])
mapAccumR f s (x:xs) = (s'', y:ys)
                       where (s'', y) = f s' x
                             (s', ys) = mapAccumR f s xs

-- Function composition

(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) f g = \x -> f (g x)

infix 8 >>
(>>) :: (a -> b) -> (b -> c) -> (a -> c)
(>>) = flip (.)

f = (((`div` 2) >> even) >> not) 4

(|>) :: b -> (b -> c) -> c
(|>) = flip ($)

f' = 4 |> div 8 |> even |> not

any, all :: (a -> Bool) -> [a] -> Bool
any pred = or . map pred 
all pred = and . map pred

elem, notElem :: Eq a => a -> [a] -> Bool
elem = any . (==)
notElem = all . (/=)

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = foldr ((++) . f) []
