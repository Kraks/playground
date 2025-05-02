import Control.Monad.ST
import Data.STRef
import Control.Monad

fibST :: Integer -> Integer
fibST n = 
  if n < 2 
  then n
  else runST $ do
    x <- newSTRef 0
    y <- newSTRef 1
    fibST' n x y
  where fibST' 0 x _ = readSTRef x
        fibST' n x y = do
          x' <- readSTRef x
          y' <- readSTRef y
          writeSTRef x y'
          writeSTRef y $! x' + y'
          fibST' (n-1) x y 

