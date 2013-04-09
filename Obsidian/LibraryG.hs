
{-# LANGUAGE ScopedTypeVariables #-}
module Obsidian.LibraryG where

import Obsidian.Array
import Obsidian.Program
import Obsidian.Exp
import Obsidian.Memory


---------------------------------------------------------------------------
-- 
--------------------------------------------------------------------------- 
mapG :: (SPull a -> BProgram (SPull b))
        -> DPull (SPull a)
        -> DPush Grid b
mapG kern as =
  Push (blocks * sizeConv n) $
  \wf ->
    do
      forAllBlocks blocks $ \bix -> do
        res <- kern (as ! bix)
        let (Push _ p) = push Block res
            wf' a ix = wf a (bix * sizeConv n + ix)
        p wf'
  where
    blocks = len as
    n = len (as ! 0) 

---------------------------------------------------------------------------
-- 
--------------------------------------------------------------------------- 
zipWithG :: (SPull a -> SPull b -> BProgram (SPull c))
           -> DPull (SPull a)
           -> DPull (SPull b)
           -> DPush Grid c
zipWithG kern as bs =
  Push (blocks * sizeConv n) $
  \wf ->
    do
      forAllBlocks blocks $ \bix -> do
        res <- kern (as ! bix) (bs ! bix)
        let (Push _ p) = push Block res
            wf' a ix = wf a (bix * sizeConv n + ix)
        p wf'
  where
    n = min m k
    -- assume uniformity
    m = len (as ! 0)
    k = len (bs ! 0)
    blocks = min (len as) (len bs) 
     

---------------------------------------------------------------------------
-- Experimental
---------------------------------------------------------------------------
zipWithG' :: forall a b c. MemoryOps c
             => (SPull a -> SPull b -> BProgram (SPull c))
             -> DPull (SPull a)
             -> DPull (SPull b)
             -> GProgram (DPush Grid c)
zipWithG' kern as bs =
  do
    snames <- forAllBlocks (sizeConv n) $ \bix ->
      do
        res <- kern (as ! bix) (bs ! bix)
        let (Push _ p) = push Block res
        p (assignArrayN n)
    let pully = Pull blocks $ \bix -> (pullFromS snames n :: Pull Word32 c)
        
    return $ Push (blocks * fromIntegral n) $
      \wf ->
      do
        forAllBlocks (sizeConv blocks) $ \bix ->
          forAll (sizeConv n) $ \tix ->
            do
              wf ((pully ! bix) ! tix) (bix * (sizeConv n) + tix)
      
  where
    n = min m k 
    -- Assume uniformity
    m = len (as ! 0)
    k = len (bs ! 0)
    blocks = (min (len as) (len bs))

