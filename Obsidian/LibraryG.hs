
{-# LANGUAGE ScopedTypeVariables #-}

module Obsidian.LibraryG where

import Obsidian.Array
import Obsidian.Program
import Obsidian.Exp
import Obsidian.Memory
import Obsidian.Library

import Control.Monad
import Data.Word

---------------------------------------------------------------------------
-- Parallel mapping  
---------------------------------------------------------------------------

pConcatMap f = pConcat . fmap f
pUnCoalesceMap f = pUnCoalesce . fmap f
pConcatMapJoin f = pConcat . fmap (pJoin.f)
pUnCoalesceMapJoin f = pUnCoalesce . fmap (pJoin.f)
pCoalesceMap n f = pUnCoalesce . fmap f . coalesce n
pSplitMap n f = pConcat . fmap f . splitUp n
pSplitMapJoin n f = pConcat . fmap (pJoin.f) . splitUp n
pMapJoin f = fmap (pJoin.f)

---------------------------------------------------------------------------
--
--------------------------------------------------------------------------- 
pConcat :: ASize l => Pull l (SPush a) -> Push l a
pConcat arr =
  Push (len arr * fromIntegral rn) $ \wf ->
    forAll (sizeConv $ len arr) $ \bix ->
      let (Push _ p) = arr ! bix
      in p (\a i -> wf a (i+bix*sizeConv rn))
  where
    rn = len $ arr ! 0

pUnCoalesce :: ASize l => Pull l (SPush a) -> Push l a
pUnCoalesce arr =
  Push (n * fromIntegral rn) $ \wf ->
    forAll (sizeConv n) $ \bix ->
      let (Push _ p) = arr ! bix
      in p (g wf)
  where
    n  = len arr
    rn = len $ arr ! 0
    s  = sizeConv rn
    g wf a i = wf a (i `div` s + (i`mod`s)*(sizeConv n))

pJoinPush :: ASize s => Program (Pull s a) -> Push s a
pJoinPush = pJoin . liftM push

pJoin :: ASize s => Program (Push s a) -> Push s a
pJoin f = Push n $ \wf -> do
    Push _ p <- f
    p wf
  where n = len $ fst $ runPrg 0 f


---------------------------------------------------------------------------
-- Parallel Generate 
---------------------------------------------------------------------------
generate :: ASize s => s -> (EWord32 -> SPush b) -> Push s b
generate n f = pConcat $ fmap f $ iterations n

