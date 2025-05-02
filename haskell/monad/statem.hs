import Control.Monad.State

data Tree a = Leaf a
            | Node (Tree a) a (Tree a)
            deriving (Show, Eq)

inc :: State Int Int
inc = state $ \i -> (i, i+1)

ntAux :: Tree a -> State Int (Tree (a, Int))
ntAux (Leaf a) = do nl <- inc
                    return (Leaf (a, nl))
ntAux (Node l n r) = do nl <- inc
                        lt <- ntAux l
                        rt <- ntAux r
                        return (Node lt (n, nl) rt)
