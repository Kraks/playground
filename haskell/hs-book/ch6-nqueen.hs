-- N Queens

positions 0 n = [[]]
positions k n = [x:xs | x <- [1..n], xs <- positions (k-1) n]

noSameRow [] = True
noSameRow (x:xs) = (not $ elem x xs) && noSameRow xs

noSameDiag [] = True
noSameDiag xs@(x:xs') = and [abs (i1 - i) /= abs (p1 - p) | (i,p) <- ip] && noSameDiag xs'
                        where (i1,p1):ip = zip [1..] xs

queens n = [xs | xs <- positions n n, noSameRow xs, noSameDiag xs]

---------

isSafe p ps = not ((elem p ps) || (sameDiag p ps))
              where sameDiag p ps = any (\(dist, q) -> abs (p-q)==dist) $ zip [1..] ps

positions' 0 n = [[]]
positions' k n = [x:xs | xs <- positions' (k-1) n, x <- [1..n], isSafe x xs]

queens' = positions'

