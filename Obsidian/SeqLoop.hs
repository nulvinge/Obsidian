{-# LANGUAGE ScopedTypeVariables #-} 

{-

   sequential loops with state
   2013 : Joel Svensson 

-}

module Obsidian.SeqLoop where


import Obsidian.Program
import Obsidian.Exp
import Obsidian.Array
import Obsidian.Memory

import Data.Word

-- TODO: Rename module to something better

---------------------------------------------------------------------------
-- seqReduce (actually reduce) 
---------------------------------------------------------------------------
seqFoldPI :: (ASize l, MemoryOps a)
          => a
          -> Pull l b
          -> (EWord32 -> a -> b -> Program a)
          -> Program a
seqFoldPI a arr f = do
  ns <- names a
  allocateScalar ns
  assignScalar ns a
  seqFor (sizeConv $ len arr) $ \ix -> do
    a' <- f ix (readFrom ns) (arr ! ix)
    assignScalar ns a'
  return (readFrom ns)

seqFoldP a arr f = seqFoldPI a arr (\i a b -> f a b)
seqFold  a arr f = seqFoldPI a arr (\i a b -> return $ f a b)
seqFoldI a arr f = seqFoldPI a arr (\i a b -> return $ f i a b)


seqReducePI1 :: (ASize l, MemoryOps a)
             => (EWord32 -> a -> a -> Program a)
             -> Pull l a
             -> Push l a
seqReducePI1 op arr =
  Push 1 $ \wf -> 
  do
    ns <- names (valType arr)
    allocateScalar ns 

    assignScalar ns init  
 
    seqFor (n-1) $ \ ix ->
      do
        v <- (op ix (readFrom ns) (arr ! (ix + 1)))
        assignScalar ns v
    
    wf (readFrom ns) 0 
  where 
    n = sizeConv$ len arr
    init = arr ! 0 

seqReduce :: (ASize l, MemoryOps a)
          => (a -> a -> a)
          -> Pull l a
          -> Push l a
seqReduce op = seqReducePI1 (\i a b -> return (op a b))

-- TODO: This is dangerous when array lengths are unknown! 

---------------------------------------------------------------------------
-- Iterate
---------------------------------------------------------------------------
seqIterate :: (ASize l, MemoryOps a)
           => EWord32
           -> (EWord32 -> a -> a)
           -> a
           -> Push l a
seqIterate n f init =
  Push 1 $  \wf -> 
  do
    ns <- names init
    allocateScalar ns 

    assignScalar ns init
    seqFor n $ \ix ->
      do
        assignScalar ns $ f ix (readFrom ns)

    wf (readFrom ns) 0 

---------------------------------------------------------------------------
-- 
---------------------------------------------------------------------------    
-- seqUntil :: MemoryOps a
--                  => (a -> a)
--                  -> (a -> EBool)
--                  -> a
--                  -> Program Thread a
-- seqUntil f p init =
--   do 
--     (ns :: Names a) <- names "v" 
--     allocateScalar ns 

--     assignScalar ns init
--     SeqWhile (p (readFrom ns)) $ 
--       do
--         (tmp :: Names a) <- names "t"
--         allocateScalar tmp
--         assignScalar tmp (readFrom ns) 
--         assignScalar ns $ f (readFrom tmp)
    
--     return $ readFrom ns


seqUntil :: (ASize l, MemoryOps a) 
         => (a -> a)
         -> (a -> EBool)
         -> a
         -> Push l a
seqUntil f p (init :: a) =
  Push 1 $ \wf -> 
  do 
    ns <- names init
    allocateScalar ns 

    assignScalar ns init
    SeqWhile (p (readFrom ns)) $ 
      do
        tmp <- names init
        allocateScalar tmp
        assignScalar tmp ((readFrom ns) :: a)
        assignScalar ns $ f (readFrom tmp)
    wf (readFrom ns) 0 

---------------------------------------------------------------------------
-- Sequential scan
---------------------------------------------------------------------------

seqScan :: (ASize l, MemoryOps a)
        => (a -> a -> a)
        -> Pull l a
        -> Push l a
seqScan op arr@(Pull n ixf)  =
  Push n $ \wf -> do
    ns <- names (valType arr)
    allocateScalar ns -- (ixf 0)
    assignScalar ns (ixf 0)
    wf (readFrom ns) 0 
    seqFor (sizeConv (n-1)) $ \ix -> do
      wf (readFrom ns) ix                  
      assignScalar ns  $ readFrom ns `op` (ixf (ix + 1))
     
                 
---------------------------------------------------------------------------
-- Sequential Map (here for uniformity) 
---------------------------------------------------------------------------

seqPush :: ASize l
        => Pull l a
        -> Push l a
seqPush arr = Push (len arr) $ \wf ->
                seqFor (sizeConv (len arr)) $ \ix ->
                  wf (arr!ix) ix 

seqMap f = seqPush . fmap f

