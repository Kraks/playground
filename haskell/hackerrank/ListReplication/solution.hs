f :: Int -> [Int] -> [Int]
f n arr = concat $ map (replicate n) arr

rep :: [Int] -> [Int]
rep (n:arr) = f n arr

main :: IO ()
main = do c <- getContents
          mapM_ print . rep . map read . words $ c

{-
main = getContents >>=
       mapM_ print. (\(n:arr) -> f n arr). map read. words
-}
