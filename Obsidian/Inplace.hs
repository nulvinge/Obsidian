{-# LANGUAGE ScopedTypeVariables,
             GADTs
             #-}

module Obsidian.Inplace where

import Obsidian.Program
import Obsidian.Exp
import Obsidian.Array
import Obsidian.Globs
import Obsidian.Memory
import Obsidian.Force
import Obsidian.Atomic
import Obsidian.Types
import Obsidian.Force
import Data.Word

--------------------------------------------------------------------------
-- Inplace
--------------------------------------------------------------------------

--data Inplace s a = Inplace s Names
data Inplace s a = Inplace s (Exp Word32 -> a -> Program ()) (Exp Word32 -> a)

inplace s ns =
  let Pull s' r = (pullFrom ns s)
  in Inplace s (flip $ assignArray ns) r

inplaceVariable s ns = Inplace s (const $ assignScalar ns) (const $ readFrom ns)

instance Array Inplace where
  resize m (Inplace _ w r) = Inplace m w r
  len      (Inplace s _ r) = s
  imap   f (Inplace s w r) = error "Cannot amap Inplace"
  ixMap  f (Inplace s w r) = Inplace s (w.f) (r.f)

instance Indexible Inplace where
  access = access.pullInplace

mkInplace :: forall a. (MemoryOps a)
          => Word32 -> Program (Inplace Word32 a)
mkInplace s = do
  snames <- names (undefined :: a)
  allocateArray snames s
  return $ inplace s snames

forceInplace :: (MemoryOps a)
             => Push Word32 a -> Program (Inplace Word32 a)
forceInplace a = do
  (p,ns) <- nameWrite a
  return $ inplace (len a) ns

pullInplace :: Inplace s a -> Pull s a
pullInplace (Inplace s w r) = Pull s r

inplaceForce :: (ASize s, MemoryOps a)
             => Inplace s a -> Push s a -> Program ()
inplaceForce (Inplace s w r) arr | s == len arr = do
  let (Push m p) = arr
  p (\a i -> w i a >> return ())
  return ()

nameWrite :: (MemoryOps a)
          => Push Word32 a -> Program (Pull Word32 a, Names)
nameWrite arr = do
  snames <- names (valType arr)
  let n = len arr
  allocateArray snames n
  let (Push m p) = arr
  p (assignArray snames)
  return $ (pullFrom snames n, snames)

nameInplaceWrite :: (MemoryOps a)
          => Push Word32 a -> Program (Inplace Word32 a, Names)
nameInplaceWrite arr = do
  snames <- names (valType arr)
  let n = len arr
  allocateArray snames n
  let (Push m p) = arr
  p (assignArray snames)
  return $ (inplace n snames, snames)

-- Atomic

inplaceAtomic f s ns =
  let Pull s' r = (pullFrom ns s)
  in Inplace s (\i a -> (atomicArray ns i f) >> return ()) r

forceInplaceAtomic :: (Scalar a)
    => Atomic a -> Push Word32 (Exp a) -> Program (Inplace Word32 (Exp a))
forceInplaceAtomic f a = do
  (p,ns) <- nameWrite a
  return $ inplaceAtomic f (len a) ns

--------------------------------------------------------------------------
-- APush
--------------------------------------------------------------------------

pusha :: (ASize l, ASize l2) => l -> l2
      -> ((EWord32 -> a -> Program ()) -> EWord32 -> Program ())
      -> Push l a
pusha l n f =
  Push l $ \wf ->
    forAll (fromIntegral n) $ \i ->
      f (flip wf) i

data APush s a = APush s ((Exp Word32 -> a -> Program ()) -> Exp Word32 -> Program ())

instance Array APush where
  resize m (APush _ p) = APush m p
  len      (APush s _) = s
  imap   f (APush s p) = APush s $ \wf i -> p (\ix e -> wf ix (f ix e)) i
  ixMap  f (APush s p) = APush s $ \wf i -> p (\ix e -> wf (f ix) e) i

{-
instance Pushable APush where
  push (APush n p) =
    Push n $ \wf -> SeqFor (sizeConv n) $ \i -> p (flip wf) i
  push (APush n p) =
    Push n $ \wf -> ForAll (sizeConv n) $ \i -> p (flip wf) i
  push Grid (APush n p) =
    Push n $ \wf -> ForAllThreads (sizeConv n) $ \i -> p (flip wf) i
-}

class APushable a where
  apush  :: ASize s => a s e -> APush s e

instance APushable APush where
  apush = id

instance APushable Pull where
  apush a = APush (len a) $ \wf i -> wf i (a!i)

{-
reducetest :: Name -> Word32 -> GProgram ()
reducetest input n = do
  o <- Output (Pointer Int)
  ForAllBlocks 1 $ \bid -> do
    s <- reducetest' input n
    ForAll 1 $ \tid -> do
      Assign o [0] (Index (s,[0]) :: Exp Int)

reducetest' :: Name -> Word32 -> BProgram Name
reducetest' i 1 = return i
reducetest' i n = do
  o <- uniqueSM
  Allocate o (n`div`2) Int
  ForAll (fromIntegral $ n`div`2) $ \tid -> do
    Assign o [tid] ((Index (i,[tid]) :: Exp Int)
                  + (Index (i,[tid+(fromIntegral $ n`div`2)])))
  reducetest' o (n`div`2)

-}


{-
seqFoldAI :: (ASize l, ASize l2, MemoryOps a)
          => (EWord32 -> a -> b -> Program a)
          -> Push l a
          -> Pull l2 b
          -> Push l a
seqFoldAI f a arr = do
  forceInplace a
  
  ns <- names (valType a)
  allocateArray ns
  assignScalar ns a
  seqFor (sizeConv $ len arr) $ \ix -> do
    a' <- f ix (readFrom ns) (arr ! ix)
    assignScalar ns a'
  return (readFrom ns)
-}

