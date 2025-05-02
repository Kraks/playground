import System.Exit

newtype Cont r a = Cont { runCont :: (a -> r) -> r }

instance Functor (Cont r) where
  fmap f (Cont rk) = Cont $ \k' -> rk (k' . f)

instance Applicative (Cont r) where
  pure v = Cont $ \k -> k v
  (Cont rk1) <*> (Cont rk2) = Cont $ \f1 -> rk1 (\f2 -> rk2 (f1 . f2))

instance Monad (Cont r) where
  return = pure
  (Cont rk) >>= f = Cont $ \k -> rk (\a -> (runCont (f a)) k)

callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC f = Cont $ \k -> runCont (f (\a -> Cont $ \_ -> k a)) k

twoC :: Cont r Int
twoC = return 2

helloC :: Cont r String
helloC = return "hello"

twoHelloC = do
  two <- twoC
  hello <- helloC
  return $ (show two) ++ hello

callCCexit = do
  val <- 
    callCC $ \e -> do
      e True 
      undefined
  return val

callCCexit2 = do
  val <- Cont $ \k -> flip runCont k $ do
    Cont $ \_ -> k True
    undefined
  return val
