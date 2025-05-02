-- 2048
import Prelude hiding (Left, Right)
import Data.List (transpose)

data Direction = Up | Down | Left | Right
data Action = Exit | Merge Direction | Invalid

ormap :: (a -> Bool) -> [a] -> Bool
ormap f [] = False
ormap f (x:xs) = f x || ormap f xs

andmap :: (a -> Bool) -> [a] -> Bool
andmap f [] = True
andmap f (x:xs) = f x && andmap f xs

merge [] = []
merge [x] = [x]
merge (0:xs) = merge xs ++ [0]
merge (x:0:xs) = merge (x:xs) ++ [0]
merge (x:x':xs) | x == x' = (x*2):xs ++ [0]
                | otherwise = x:merge (x':xs)

mergeLineLeft = merge
mergeLineRight = reverse . mergeLineLeft . reverse
mergeLeft = map mergeLineLeft
mergeRight = map mergeLineRight
mergeUp = transpose . mergeLeft . transpose
mergeDown = transpose . mergeRight .transpose

move Left = mergeLeft
move Right = mergeRight
move Up = mergeUp
move Down = mergeDown

winNumber = 2048
isWin = ormap $ ormap $ (== winNumber)
isLineFail xs = andmap (\p -> not (fst p == snd p || 0 == fst p || 0 == snd p)) zipped
                where zipped = zip (take k xs) (drop 1 xs)
                      k = length xs - 1
isFail g = (andmap isLineFail g) && (andmap isLineFail (transpose g))

listSet [] _ _ = []
listSet (x:xs) 0 ele = ele:xs
listSet (x:xs) n ele = x:listSet xs (n-1) ele

showLine [] = ""
showLine (x:xs) = show x ++ " " ++ showLine xs

showGrid [] = ""
showGrid (l:ls) = showLine l ++ "\n" ++ showGrid ls

strToAction "w" = Merge Up
strToAction "a" = Merge Left
strToAction "s" = Merge Down
strToAction "d" = Merge Right
strToAction "q" = Exit
strToAction  _  = Invalid

emptyGrid n = take n $ repeat $ take n $ repeat 0
