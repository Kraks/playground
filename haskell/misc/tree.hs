data Tree a = Leaf a | Branch (Tree a) (Tree a)

showTree :: (Show a) => Tree a -> String
showTree (Leaf x)     = show x
showTree (Branch l r) = "<" ++ showTree l ++ "|" ++ showTree r ++ ">"

showsTree :: (Show a) => Tree a -> ShowS
showsTree (Leaf x)     = shows x
showsTree (Branch l r) = ('<':) . showsTree l . ('|':) . showsTree r . ('>':)


readsTree               :: (Read a) => ReadS (Tree a)
readsTree ('<':s)       =  [(Branch l r, u) | (l, '|':t) <- readsTree s,
                                              (r, '>':u) <- readsTree t ]
readsTree s             =  [(Leaf x, t)     | (x,t)      <- reads s]

instance Show a => Show (Tree a) where
    showsPrec _ x = showsTree x

instance Read a => Read (Tree a) where
   readsPrec _ s = readsTree s

t :: Tree Int
t = read "<1|2>"
