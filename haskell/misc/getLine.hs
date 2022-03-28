getLine1 :: IO String
getLine1 = do c <- getChar
              if c == '\n'
                  then return ""
                  else do l <- getLine
                          return (c:l)

sequence_1 :: [IO ()] -> IO ()
sequence_1 = foldr (>>) (return ())

putStr1 :: String -> IO ()
putStr1 s = sequence_1 (map putChar s)

main :: IO ()
main = do l <- getLine
          putStr1 l
