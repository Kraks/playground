import Control.Applicative
import Control.Monad
import System.IO

main :: IO ()
main = do n_temp <- getLine
          let n = read n_temp :: Int
          forM_ [1..n] $ \a0 -> do x_temp <- getLine
                                   let x = read x_temp :: Double

getMultipleLines :: Int -> IO [String]
getMultipleLines n
  | n <= 0 - return []
  | otherwise = do x <- getLine
                   xs <- getMultipleLines (n-1)
                   return (x:xs)
