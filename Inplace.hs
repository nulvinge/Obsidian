{-# LANGUAGE ScopedTypeVariables,
             GADTs
             #-}

module Inplace where

import Obsidian.Program
import Obsidian.Exp
import Obsidian.Array
import Obsidian.Globs
import Obsidian.Memory
import Obsidian.Force
import Data.Word

---------------------------------------------------------------------------
-- Inplace
--------------------------------------------------------------------------- 

data Inplace s a = Inplace s Names

mkInplace :: forall a. (MemoryOps a)
          => Word32 -> BProgram (Inplace Word32 a)
mkInplace s = do
  snames <- names (undefined :: a)
  allocateArray snames (undefined :: a) s
  return $ Inplace s snames

writeInplace a = do
  (p,ns) <- nameWrite a
  return $ Inplace (len a) ns

forceInplace a = writeInplace a >>= idSync

pullInplace (Inplace s ns) = pullFrom ns s

nameWrite :: forall a p. (Array p, Pushable p, MemoryOps a)
          => p Word32 a -> BProgram (Pull Word32 a, Names)
nameWrite arr = do
  snames <- names (undefined :: a)
  let n = len arr
  allocateArray snames (undefined :: a) n
  let (Push m p) = push Block arr
  p (assignArray snames)
  return $ (pullFrom snames n, snames)

---------------------------------------------------------------------------
-- APushable
--------------------------------------------------------------------------- 

data APush s a = APush s ((a -> Exp Word32 -> TProgram ()) -> Exp Word32 -> TProgram ())

instance Array (APush) where
  resize m (APush _ p) = APush m p
  len      (APush s _) = s
  aMap   f (APush s p) = APush s $ \wf i -> p (\e ix -> wf (f e) ix) i
  ixMap  f (APush s p) = APush s $ \wf i -> p (\e ix -> wf e (f ix)) i

instance Pushable APush where
  push Thread (APush n p) =
    Push n $ \wf -> SeqFor (sizeConv n) $ \i -> p wf i
  push Block (APush n p) =
    Push n $ \wf -> ForAll (sizeConv n) $ \i -> p wf i
  push Grid (APush n p) =
    Push n $ \wf -> ForAllThreads (sizeConv n) $ \i -> p wf i

class APushable a where
  apush  :: ASize s => a s e -> APush s e

instance APushable APush where
  apush = id

instance APushable Pull where
  apush a = APush (len a) $ \wf i -> wf (a!i) i

