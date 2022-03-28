sumoddHelper [] acc = acc
sumoddHelper (x:xs) acc 
  | x `mod` 2 == 0 = sumoddHelper xs acc
  | otherwise = sumoddHelper xs (acc + x)

sumodd xs = sumoddHelper xs 0

main = do
  inputdata <- getContents
  putStrLn $ show $ sumodd $ map (read :: String -> Int) $ lines inputdata
