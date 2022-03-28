-- Chapter 11, System Programming and IO

{-
main :: IO ()
main = do putStr "What's your name? "
          name <- getLine
          putStrLn $ "Hello " ++ name
-}

main :: IO [Char]
main = putStr "What's your name? " >>= \p1 ->
       getLine >>= \name ->
       putStrLn ("Hello " ++ name) >>= \p2 -> 
       return name
