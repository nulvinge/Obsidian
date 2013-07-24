
{-# LANGUAGE ScopedTypeVariables #-}

module Obsidian.LibraryG where

import Obsidian.Array
import Obsidian.Program
import Obsidian.Exp
import Obsidian.Memory
import Obsidian.Library

import Data.Word

---------------------------------------------------------------------------
-- Parallel mapping  
---------------------------------------------------------------------------

-- pConcatMap :: ASize l
--          => (SPull a -> Program t (SPush t b))
--          -> Pull l (SPull a)
--          -> Push (Step t) l b
-- pConcatMap f as = 
--   Push (n * fromIntegral rn) $
--     \wf ->
--     do
--       forAll (sizeConv n) $ \tix -> do
--         (Push _ p) <- f (as ! tix)
--         let wf' a ix = wf a (tix * sizeConv rn + ix)
--         p wf'      
--     where
--       n = len as
--       rn = len $ fst $ runPrg 0 (f (as ! 0))
--       m = len (as ! 0)

pConcatMap f = pConcat . pMap f
pUnCoalesceMap f = pUnCoalesce . pMap f

---------------------------------------------------------------------------
--
--------------------------------------------------------------------------- 
pMap :: ASize l
         => (SPull a -> SPush b)
         -> Pull l (SPull a)
         -> Pull l (SPush b) 
pMap f as =
  mkPullArray (len as) $ \bix -> 
    ixMap (+bix*sizeConv rn) $ f (as ! bix)
  where
    rn = len $ (f (as ! 0))

pConcat :: ASize l => Pull l (SPush a) -> Push l a
pConcat arr =
  Push (len arr * fromIntegral rn) $ \wf -> do
    forAll (sizeConv $ len arr) $ \bix ->
      let (Push _ p) = arr ! bix
      in p wf
  where
    rn = len $ arr ! 0

pUnCoalesce :: ASize l => Pull l (SPush a) -> Push l a
pUnCoalesce arr =
  Push (n * fromIntegral rn) $ \wf ->
  do
    forAll (sizeConv n) $ \bix ->
      let (Push _ p) = arr ! bix
      in p (g wf)
  where
    n  = len arr
    rn = len $ arr ! 0
    s  = sizeConv rn
    g wf a i = wf a (i `div` s + (i`mod`s)*(sizeConv n))

pJoin :: ASize s => Program (Push s a) -> Push s a
pJoin f = Push n $ \wf -> do
    Push _ p <- f
    p wf
  where n = len $ fst $ runPrg 0 f


---------------------------------------------------------------------------
-- Parallel ZipWith 
---------------------------------------------------------------------------

pZipWith :: ASize l => (SPull a -> SPull b -> SPush c)
           -> Pull l (SPull a)
           -> Pull l (SPull b)
           -> Pull l (SPush c)
pZipWith f as bs =
  Pull instances $ \ bix -> 
    ixMap (+bix*sizeConv n) $ f (as!bix) (bs!bix)
    where
      n = min m k 
      m = len (as ! 0)
      k = len (bs ! 0)
      instances = min (len as) (len bs) 


-- pZipWith :: ASize l => (SPull a -> SPull b -> Program t (SPush t c))
--            -> Pull l (SPull a)
--            -> Pull l (SPull b)
--            -> Push (Step t) l c
-- pZipWith f as bs =
--     Push (instances * fromIntegral rn) $
--     \wf ->
--     do
--       forAll (sizeConv instances) $ \tix -> do
--         (Push _ p) <- f (as ! tix) (bs ! tix) 
--         let wf' a ix = wf a (tix * sizeConv n + ix)
--         p wf'      

--     where
--       -- Is this ok?! (does it break?) 
--       rn = len $ fst $ runPrg 0 (f (as ! 0) (bs ! 0))
--       n = min m k 

--       m  = len (as ! 0)
--       k  = len (bs ! 0)
--       instances = min (len as) (len bs) 


---------------------------------------------------------------------------
-- Parallel Generate 
---------------------------------------------------------------------------
generate :: ASize s => s -> (EWord32 -> SPush b) -> Push s b
generate n f = pConcat $ fmap f $ iterations n

