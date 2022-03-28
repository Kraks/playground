{-# LANGUAGE RecursiveDo #-}

import Control.Monad.Fix

data RoseTree a = RoseTree a [RoseTree a]
  deriving Show

exampleTree :: RoseTree Int
exampleTree = RoseTree 5 [RoseTree 4 [], RoseTree 7 []]

pureMax :: Ord a => RoseTree a -> RoseTree (a, a)
pureMax tree = 
  let (t, largest) = go largest tree 
   in t
  where
    go :: Ord a => a -> RoseTree a -> (RoseTree (a, a), a)
    go biggest (RoseTree x []) = (RoseTree (x, biggest) [], x)
    go biggest (RoseTree x xs) = 
      let sub = map (go biggest) xs
          (xs', largests) = unzip sub
       in (RoseTree (x, biggest) xs', max x (maximum largests))

impureMin :: (MonadFix m, Ord b) => (a -> m b) -> RoseTree a -> m (RoseTree (a, b))
impureMin f tree = do
  rec (t, largest) <- go largest tree
  return t
  where
    go smallest (RoseTree x []) = do
      b <- f x
      return (RoseTree (x, smallest) [], b)
    go smallest (RoseTree x xs) = do
      sub <- mapM (go smallest) xs
      b <- f x
      let (xs', bs) = unzip sub
      return (RoseTree (x, smallest) xs', min b (minimum bs))

budget :: String -> IO Int
budget "Ada" = return 10
budget "Curry" = return 50
budget "Dijkstra" = return 20
budget "Howard" = return 5
budget _ = return 999

inviteTree = RoseTree "Ada" [ RoseTree "Dijkstra" []
                            , RoseTree "Curry" [ RoseTree "Howard" []]
                            ]
