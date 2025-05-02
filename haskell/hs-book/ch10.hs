-- Ch10, Monad

import Prelude hiding (Monad, (>>=), return, (>>))

data Exp = Lit Integer
         | Add Exp Exp
         | Sub Exp Exp
         | Mul Exp Exp
         | Div Exp Exp

eval (Lit n) = n
eval (Add l r) = eval l + eval r
eval (Sub l r) = eval l - eval r
eval (Mul l r) = eval l * eval r
eval (Div l r) = eval l `div` eval r

evalSeq :: Maybe Integer -> (Integer -> Maybe Integer) -> Maybe Integer
evalSeq mi f = case mi of Nothing -> Nothing
                          Just a -> f a
-- some tests
nothing = Just 5 `evalSeq` (\x -> (Just 6 `evalSeq` (\y -> Nothing)))
eleven = Just 5 `evalSeq` \x -> 
         Just 6 `evalSeq` \y -> 
         Just (x+y)

safeEval (Add l r) = safeEval l `evalSeq` \n1 ->
                     safeEval r `evalSeq` \n2 ->
                     Just (n1 + n2)
safeEval (Sub l r) = safeEval l `evalSeq` \n1 ->
                     safeEval r `evalSeq` \n2 ->
                     Just (n1 - n2)
safeEval (Mul l r) = safeEval l `evalSeq` \n1 ->
                     safeEval r `evalSeq` \n2 ->
                     Just (n1 * n2)
safeEval (Div l r) = safeEval l `evalSeq` \n1 ->
                     safeEval r `evalSeq` \n2 ->
                     if n2 == 0 then Nothing else Just (n1 `div` n2)

-- Identity Monad
class Monad m where
  (>>=) :: m a -> (a -> m b) -> m b -- bind
  return :: a -> m a
  
  (>>) :: m a -> m b -> m b
  m >> k = m >>= \_ -> k

  fail :: String -> m a
  fail s = error s

newtype Identity a = Identity { runIdentity :: a } deriving Show

instance Monad Identity where
  return a = Identity a
  (>>=) (Identity m) k = k m

-- some tests
-- not $ odd $ 5
idfalse = Identity 5 >>= \x -> Identity (odd x) >>= \x -> Identity (not x)

(|>) = flip ($)
f = 5 |> \x -> odd x |> \x -> not x

-- Monad Laws

-- Left identity
-- return x >>= f = f x

-- Right identity
-- m >>= return  = m

-- Associative
-- (m >>= f) >>= g = m >>= (\x -> f x >>= g)


-- List as Monad

instance Monad [] where
  return x = [x]
  xs >>= f = concatMap f xs
  fail _ = []

plus :: Num a => [a] -> [a] -> [a]
plus xs ys = do x <- xs
                y <- ys
                return (x+y)
        
alist = plus [1,2,3] [4,5,6] 

plus' :: Num a => [a] -> [a] -> [a]
plus' xs ys = xs >>= \x ->
              ys >>= \y ->
              return (x+y)

-- Some Monad operator
-- <=<, >>=, >=>

