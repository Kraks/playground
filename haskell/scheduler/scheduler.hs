-- https://osa1.net/posts/2017-10-16-a-parallel-scheduler.html

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Concurrent.Async.Lifted.Safe
import Control.Concurrent.MVar.Lifted
import Control.Concurrent.Timeout
import Control.Exception.Lifted
import Control.Monad
import Control.Monad.Logger.CallStack hiding (defaultLogStr)
import Control.Monad.Trans.Control

import Data.Function
import Data.IORef
import Data.Monoid
import Data.Ord
import qualified Data.Set as S
import qualified Data.Text as T

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import System.Log.FastLogger

newtype Unique = Unique Int
  deriving (Eq, Ord)

------------------------------------------------------------------------------

data Resource = Resource
  { _resourceName :: T.Text
  , _resourceId   :: Unique
  , _resourceLock :: MVar()
  }

instance Show Resource where
  show = T.unpack . _resourceName

instance Eq Resource where
  (==) = (==) `on` _resourceId

instance Ord Resource where
  compare = compare _resourceId

withResources :: (MonadLogger m, MonadBaseControl IO m) => S.Set Resource -> m () -> m ()
withResources locks a = acquire_locks (S.toList locks)
  where acquire_locks ls = case ls of
          [] -> a
          l:ls' -> do
            logDebug ("taking lock" <> (_resourceName l))
            withMVar (_resourceLock l) $ \() ->
              acquire_locks ls'

------------------------------------------------------------------------------

newtype Task = Task
  { runTask :: forall m . (MonadLogger m, MonadBaseControl IO m) => m () }

mkFaskTask :: Int -> S.Set Resource -> Task
mkFaskTask i res =
  Task $ withResources res $ do
    logDebug ("Performing " <> T.pack (show i))
    threadDelay (500 :: Milliseconds)
    logDebug ("Fast task done (" <> T.pack (show i) <> ")")

mkSlowTask :: Int -> S.Set Resource -> Task
mkSlowTask i res =
  Task $ withResources res $ do
    logDebug ("Performing " <> T.pack (show i))
    threadDelay (3 :: Seconds)
    logDebug ("Fast task done (" <> T.pack (show i) <> ")")

mkCrashingTask :: Int -> S.Set Resource -> Task
mkCrashingTask i res =
  Task $ withResources res $ do
    logDebug ("Performing " <> T.pack (show i))
    error "task failed"

------------------------------------------------------------------------------

newtype UniqueGen = UniqueGen (IORef Int)

mkUniqGen :: IO UniqueGen
mkUniqGen = UniqueGen <$> newIORef 0

mkUniq :: UniqueGen -> IO Unique
mkUniq (UniqueGen ref) = atomicModifyIORef' ref (\i -> (i+1, Unique i))

genResources :: Int -> IO [Resource]
genResources n =
  forM [0 .. n] $ \i -> do
    lock <- newMVar() -- initial full
    return $ Resource
      { _resourceName = T.pack ("resource" ++ show i)
      , _resourceId   = Unique i
      , _resourceLock = lock
      }

genTaskRes :: MonadGen m => [Resource] -> Int -> m [S.Set Resource]
genTaskRes res n = replicateM n (genTaskRes' res)

genTaskRes' :: MonadGen m => [Resource] -> m (S.Set Resource)
genTaskRes' res = Gen.set (Range.linear 1 (length res)) (Gen.element res)

------------------------------------------------------------------------------

schedule :: (MonadLogger m, MonadBaseControl IO m, Forall (Pure m)) => [Task] -> m ()
schedule tasks = do
  thrs <- forM tasks $ \(Task task) ->
    async (task `catch` (\(e :: SomeException) -> logDebug "Task failed"))
  forM_ thrs wait

