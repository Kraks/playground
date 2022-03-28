-- Chapter 12, MonadWriter

{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies #-}

import Control.Monad.Writer
import Control.Monad.Writer.Class

left', right' :: Int -> Writer String Int
left' x = writer (x-1, "move left\n")
right' x = writer (x+1, "move right\n")

{-
class (Monoid w, Monad m) => MonadWriter w m | m -> w where
  tell :: w -> m ()
  listen :: m a -> m (a, w)
  pass :: m (a, w -> w) -> m a
-}

move i = do x <- left' i
            tell "move left once!\n gonna move again\n"
            y <- left' x
            return y

two = runWriter $ move 4

move' i = left' i >>= \x ->
          tell "move left once!\n gonna move again\n" >>= \dummy ->
          left' x >>= \y ->
          return y

two' = runWriter $ move' 4


