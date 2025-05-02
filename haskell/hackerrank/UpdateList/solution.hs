f arr = map (\x -> if x < 0 then -1 * x else x) arr

main = do
  inputdata <- getContents
  mapM_ putStrLn $ map show $ f $ map (read :: String -> Int) $ lines inputdata
