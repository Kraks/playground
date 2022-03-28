-- Ch11, Printf

{-# LANGUAGE FlexibleInstances #-}

format :: Show t => String -> t -> String
format ('%':'s':cs) cs' = show cs' ++ cs
format (c:cs) cs' = c : format cs cs'
format "" cs' = ""

class Printf t where
  printf :: String -> t

instance Printf (IO ()) where
  printf cs = putStrLn cs

instance (Show u, Printf t) => Printf (u -> t) where
  printf cs = \x -> printf (format cs x)

test1 :: IO ()
test1 = printf "%s and %s" "Hello" "World"
