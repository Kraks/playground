rev [] = []
rev (x:xs) = rev xs ++ [x]

main = do 
  inputdata <- getContents
  let numbers = map read (lines inputdata) :: [Int]
  putStrLn $ unlines $ map show $ rev numbers
