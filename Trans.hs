
{-# LANGUAGE ScopedTypeVariables,
             FlexibleContexts #-} 

module Examples where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian.Program
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Array
import Obsidian.Library
import Obsidian.Force
import Obsidian.CodeGen.InOut
import Obsidian.Atomic

import Data.Word
import Data.Int
import Data.Bits

import qualified Data.Vector.Storable as V

import Control.Monad.State

import Prelude hiding (zipWith,sum,replicate)
import qualified Prelude as P 
import Debug.Trace

---------------------------------------------------------------------------
-- Util 
---------------------------------------------------------------------------
quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 

---------------------------------------------------------------------------
-- Scalar argument
---------------------------------------------------------------------------
scalArg :: EInt -> GlobPull EInt -> Final (GProgram (GlobPull EInt)) 
scalArg e = forceG . mapG (force . fmap (+e)) 256

getScalArg = quickPrint scalArg ((variable "X") :->
                                 undefinedGlobal)

---------------------------------------------------------------------------
-- MapFusion example
---------------------------------------------------------------------------

mapFusion :: Pull EInt -> BProgram (Pull EInt)
mapFusion arr =
  do
    imm <- sync $ (fmap (+1) . fmap (*2)) arr
    sync $ (fmap (+3) . fmap (*4)) imm 

input1 :: Pull EInt 
input1 = namedArray "apa" 32

input2 :: GlobPull EInt
input2 = namedGlobal "apa" 

input3 :: GlobPull (Exp Int32)
input3 = namedGlobal "apa" 



---------------------------------------------------------------------------
-- Small experiments 
---------------------------------------------------------------------------

sync :: Forceable a => a -> BProgram (Forced a)
sync = force 

prg0 = putStrLn$ printPrg$  mapFusion input1

mapFusion' :: GlobPull EInt
              -> GlobPush EInt
mapFusion' arr = mapG mapFusion 256 arr
                 
prg1 = putStrLn$ printPrg$ cheat $ (forceG . mapFusion') input2

prg2 = quickPrint (forceG . mapFusion') input2

---------------------------------------------------------------------------
-- Transpose experiments 
---------------------------------------------------------------------------

transF :: (Exp Word32) -> (Exp Word32) -> (Exp Word32)
transF w i = w*x + y
  where y = (i `div` w)
        x = (i `mod` w)

--wrong
trans1 :: Exp Word32 -> Pull a -> Pull a
trans1 w arr = ixMap (transF w) arr
t1 = quickPrint (forceG.mapG (return . trans1 256) 16) input2


--the same thing as trans1
trans2 :: Exp Word32 -> Word32 -> GlobPull a -> GlobPush a
trans2 w n (GlobPull ixf) = 
    GlobPush $ \wf ->
        ForAllBlocks $ \bix -> do
            let ixf' = ((\ix -> ixf (bix * fromIntegral n + ix)).(transF w))
            let res = Pull n ixf'
            ForAll (Just n) $ \ix -> wf (res ! ix) (bix * fromIntegral n + ix)
t2 = quickPrint (forceG.trans2 256 16) input2

--this time correct
trans3 :: Exp Word32 -> Word32 -> GlobPull a -> GlobPush a
trans3 w n (GlobPull ixf) = 
    GlobPush $ \wf ->
        ForAllBlocks $ \bix -> do
            let ixf' = ixf.(transF w)
            let res = Pull n ixf'
            ForAll (Just n) $ \ix -> wf (res ! (bix * fromIntegral n + ix)) (bix * fromIntegral n + ix)
t3 = quickPrint (forceG.trans3 256 16) input2

mapGid :: (Pull a -> BProgram (Pull b))
        -> Word32 -- BlockSize ! 
        -> GlobPull a
        -> GlobPush b
mapGid f n (GlobPull ixf)  =
  GlobPush
    $ \wf ->
      ForAllBlocks
       $ \bix ->
         do -- BProgram do block 
           let pully = Pull n ixf --this n is wrong
           res <- f pully
           ForAll (Just n) $ \ix ->
             wf (res ! (bix * fromIntegral n + ix)) (bix * fromIntegral n + ix)

--reuse trans1

t4 = quickPrint (forceG.mapGid (return . trans1 256) 16) input2

mapGidP :: (Pull a -> BProgram (Push b))
        -> Word32 -- BlockSize ! 
        -> GlobPull a
        -> GlobPush b
mapGidP f n (GlobPull ixf)  =
  GlobPush
    $ \wf ->
      ForAllBlocks
       $ \bix ->
         do -- BProgram do block 
           let bx = bix * fromIntegral n
           let pully = Pull n (ixf.(bx+)) --this n is wrong
           Push n' pf <- f pully
           --let wf' a ix = wf a (bx+ix)
           pf (\a ix -> wf a (bx+ix))
           
           --ForAll (Just n') $ \ix ->
           --  wf (res ! (bix * fromIntegral n + ix)) (bix * fromIntegral n + ix)

t5 = quickPrint (forceG.mapGid (force . push . trans1 256) 16) input2

t6 = quickPrint (forceG.mapGidP (return . push . trans1 256) 16) input2

block :: Pull a -> Push a
block (Pull b ixf) = Push b $ \wf -> do
    ForAll (Just b) $ \ix ->
        SeqFor m $ \ixs -> do
            wf (ixf (ixs*bl + ix)) (ixs*bl + ix)
    where bl = fromIntegral b
          m = fromIntegral b --(n `div` b)

trans7 :: Word32 -> Pull (Exp a) -> Push (Exp a)
trans7 w = block.ixMap (transF (Literal w))

--wrong
t7 = quickPrint (forceG.mapGidP (return . trans7 256) 16) input2

blockGid :: Pull a -> GlobPush a
blockGid (Pull b ixf) = GlobPush $ \wf -> do
    ForAllBlocks $ \bx ->
        ForAll (Just b) $ \ix ->
            SeqFor m $ \ixs -> do
                let i = bx*fromIntegral b + ix
                wf (ixf (ixs*bl + i)) (ixs*bl + i)
        where bl = fromIntegral b
              m = fromIntegral b --(n `div` b)

unGlobal :: Word32 -> GlobPull a -> Pull a
unGlobal n (GlobPull ixf) = Pull n ixf

trans8 w = blockGid.ixMap (transF (Literal w))
t8 = quickPrint (forceG .trans8 256.(unGlobal 16)) input2

