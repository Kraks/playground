{-# LANGUAGE ScopedTypeVariables #-}

import qualified Control.Monad.Trans.Cont  as C
import           Control.Monad.Trans.Class (lift)
import           System.Random             as R

goto = C.callCC $ \k -> let f = k f
                        in return f

gotoC = C.callCC $ \k -> let f n = k (f, n)
                         in return (f, 0)

gotoEx1 = flip C.runContT return $ do
  lb1 <- goto
  lift $ putStrLn "one"
  lb2 <- goto
  lift $ putStrLn "two"
  (num :: Int) <- lift $ R.randomRIO (0, 2)
  if num < 1 then lb1
  else if num < 2 then lb2
  else lift $ putStrLn "done"

gotoEx2 = flip C.runContT return $ do
  (lb, num) <- gotoC
  lift $ putStrLn ("count: " ++ show num)
  if num < 10 then lb (num + 1)
  else lift $ putStrLn "done"
