f :: [Int] -> [Int]
f [] = []
f (x:[]) = []
f (x:y:tl) = y:(f tl)

main = do
  inputdate <- getContents
  mapM_ (putStrLn . show) . f . map read . lines $ inputdate
