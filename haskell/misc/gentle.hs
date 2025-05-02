quicksort [] = []
quicksort (x : xs) = quicksort [y | y <- xs, y < x] ++ [x] ++ quicksort [y | y <- xs, y >= x]

add = \x y -> x + y

(.) :: (b -> c) -> (a -> b) -> (a -> c)
f . g = \x -> f (g x)

class Eq a where
   (==), (/=) :: a -> a -> Bool
   x /= y     =  not (x == y)
   --x == y     =  not (x /= y)
