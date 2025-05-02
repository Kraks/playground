module Floyd (floyd_warshall) where
-- https://www.schoolofhaskell.com/user/mandu/shortest-path-floyd-warshall

import Data.List (transpose)

floyd_warshall start end graph = (dist, [start] ++ route ++ [end])
  where dist = shortest (start, end, length graph) graph
        route = path (start, end, length graph) graph

-- Calculates the value of the shortest route
shortest (i, j, 0) g = g !! (i-1) !! (j-1)
shortest (i, j, k) g = min (shortest (i, j, k - 1) g) $
                           (shortest (i, k, k - 1) g) + (shortest (k, j, k - 1) g)

-- Reconstructs the shortest path
path (i, j, 0) _ = []
path (i, j, k) g
  | direct < step = path (i, j, k - 1) g
  | otherwise = (path (i, k, k - 1) g) ++ [k] ++ (path (k, j, k-1) g)
  where direct = shortest (i, j, k - 1) g
        step = (shortest (i, k, k - 1) g) + (shortest (k, j, k - 1) g)

main = do
  -- show Example problem
  contents <- readFile "graph.txt"
  let graph = readGraph contents

  output $ floyd_warshall 1 8 graph
  -- /show

output x = do
  putStrLn $ "(Length, [nodes])"
  putStrLn $ show x

readGraph = transpose . str2int . map words . lines
str2int = map.map $ zero2inf . fromIntegral . (\xs -> read xs :: Int)
zero2inf x = if x == 0 then 1/0 else x
