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
import Obsidian.Names

import Data.Word

-- TODO: Rename module to something better

---------------------------------------------------------------------------
-- seqReduce (actually reduce) 
---------------------------------------------------------------------------
seqReduceTI :: (ASize l, MemoryOps a)
           => (EWord32 -> a -> a -> TProgram a)
           -> Pull l a
           -> Push Thread l a
seqReduceTI op arr =
  Push 1 $ \wf -> 
  do
    ns <- names (valType arr)
    allocateScalar ns 

    assignScalar ns init  
 
    SeqFor (n-1) $ \ ix ->
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
           -> Push Thread l a
seqReduce op = seqReduceTI (\i a b -> return (op a b))

-- TODO: This is dangerous when array lengths are unknown! 

---------------------------------------------------------------------------
-- Iterate
---------------------------------------------------------------------------
seqIterate :: (ASize l, MemoryOps a)
              => EWord32
              -> (EWord32 -> a -> a)
              -> a
              -> Push Thread l a
seqIterate n f init =
  Push 1 $  \wf -> 
  do
    ns <- names init
    allocateScalar ns 

    assignScalar ns init
    SeqFor n $ \ix ->
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
            -> Push Thread l a
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
           -> Push Thread l a
seqScan op arr@(Pull n ixf)  =
  Push n $ \wf -> do
    ns <- names (valType arr)
    allocateScalar ns -- (ixf 0)
    assignScalar ns (ixf 0)
    wf (readFrom ns) 0 
    SeqFor (sizeConv (n-1)) $ \ix -> do
      wf (readFrom ns) ix                  
      assignScalar ns  $ readFrom ns `op` (ixf (ix + 1))
     
                 
---------------------------------------------------------------------------
-- Sequential Map (here for uniformity) 
---------------------------------------------------------------------------

seqMap :: ASize l
          => (a -> b)
          -> Pull l a
          -> Push Thread l b
seqMap f arr =
  Push (len arr) $ \wf -> do
    SeqFor (sizeConv (len arr)) $ \ix ->
      wf (f (arr ! ix)) ix 


