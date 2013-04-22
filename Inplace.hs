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

--------------------------------------------------------------------------
-- Inplace
--------------------------------------------------------------------------

--data Inplace s a = Inplace s Names
data Inplace s a = Inplace s (Exp Word32 -> a -> TProgram ()) (Exp Word32 -> a)

inplace s ns =
  let Pull s' r = (pullFrom ns s)
  in Inplace s (flip $ assignArray ns) r

inplaceVariable s ns = Inplace s (const $ assignScalar ns) (const $ readFrom ns)

instance Indexible Inplace where
  access = access.pullInplace

mkInplace :: forall a. (MemoryOps a)
          => Word32 -> BProgram (Inplace Word32 a)
mkInplace s = do
  snames <- names (undefined :: a)
  allocateArray snames (undefined :: a) s
  return $ inplace s snames

writeInplace :: (Pushable p, Array p, MemoryOps a)
             => p Word32 a -> BProgram (Inplace Word32 a)
writeInplace a = do
  (p,ns) <- nameWrite a
  return $ inplace (len a) ns

forceInplace a = writeInplace a >>= idSync

pullInplace :: Inplace s a -> Pull s a
pullInplace (Inplace s w r) = Pull s r

inplaceWrite :: (Pushable p, Array p, ASize s, MemoryOps a)
             => Inplace s a -> p s a -> Program Block ()
inplaceWrite (Inplace s w r) arr | s == len arr = do
  let (Push m p) = push Block arr
  p (flip w)
  return ()

inplaceForce i arr = inplaceWrite i arr >>= idSync

nameWrite :: forall a p. (Array p, Pushable p, MemoryOps a)
          => p Word32 a -> BProgram (Pull Word32 a, Names)
nameWrite arr = do
  snames <- names (undefined :: a)
  let n = len arr
  allocateArray snames (undefined :: a) n
  let (Push m p) = push Block arr
  p (assignArray snames)
  return $ (pullFrom snames n, snames)

nameInplaceWrite :: forall a p. (Array p, Pushable p, MemoryOps a)
          => p Word32 a -> BProgram (Inplace Word32 a, Names)
nameInplaceWrite arr = do
  snames <- names (undefined :: a)
  let n = len arr
  allocateArray snames (undefined :: a) n
  let (Push m p) = push Block arr
  p (assignArray snames)
  return $ (inplace n snames, snames)


--------------------------------------------------------------------------
-- APush
--------------------------------------------------------------------------

data APush s a = APush s ((Exp Word32 -> a -> TProgram ()) -> Exp Word32 -> TProgram ())

instance Array (APush) where
  resize m (APush _ p) = APush m p
  len      (APush s _) = s
  aMap   f (APush s p) = APush s $ \wf i -> p (\ix e -> wf ix (f e)) i
  ixMap  f (APush s p) = APush s $ \wf i -> p (\ix e -> wf (f ix) e) i

instance Pushable APush where
  push Thread (APush n p) =
    Push n $ \wf -> SeqFor (sizeConv n) $ \i -> p (flip wf) i
  push Block (APush n p) =
    Push n $ \wf -> ForAll (sizeConv n) $ \i -> p (flip wf) i
  push Grid (APush n p) =
    Push n $ \wf -> ForAllThreads (sizeConv n) $ \i -> p (flip wf) i

class APushable a where
  apush  :: ASize s => a s e -> APush s e

instance APushable APush where
  apush = id

instance APushable Pull where
  apush a = APush (len a) $ \wf i -> wf i (a!i)

