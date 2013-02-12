
{-# LANGUAGE ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
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

input2 :: GlobPull EInt
input2 = namedGlobal "apa" 

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

block :: Exp Word32 -> Exp Word32 -> Pull a -> Push a
block w m (Pull b ixf) = Push b $ \wf -> do
    ForAll (Just b) $ \ix ->
        SeqFor m $ \ixs -> do
            wf (ixf (ixs*w + ix)) (ixs*w + ix)

trans7 :: Exp Word32 -> Pull (Exp a) -> Push (Exp a)
trans7 w = block w w.ixMap (transF w)

--wrong
t7 = quickPrint (forceG.mapGidP (return . trans7 256) 16) input2

blockGid :: Exp Word32 -> Exp Word32 -> Pull a -> GlobPush a
blockGid w m (Pull b ixf) = GlobPush $ \wf -> do
    ForAllBlocks $ \bx ->
        ForAll (Just b) $ \ix ->
            SeqFor m $ \ixs -> do
                let i = bx*fromIntegral b + ix
                wf (ixf (ixs*w + i)) (ixs*w + i)

unGlobal :: Word32 -> GlobPull a -> Pull a
unGlobal n (GlobPull ixf) = Pull n ixf

--finally a somewhat correct version
trans8 w = blockGid w w.ixMap (transF w)
t8 = quickPrint (forceG .trans8 256.(unGlobal 16)) input2

--type 1 implemenation

blockT :: Exp Word32 -> Exp Word32 -> Pull a -> Push a
blockT w m p = Push (len p) $ \wf ->
    ForAll Nothing $ \ix ->
        SeqFor m $ \ixs -> do
            wf (p ! (ixs*w + ix)) (ixs*w + ix)


blockB :: Exp Word32 -> Exp Word32 -> Word32 -> (Pull a -> Push a) -> GlobPull a -> GlobPush a
blockB w h b f (GlobPull ixf) = GlobPush $ \wf ->
    ForAllBlocks $ \ixb -> do
        let Push n pwf = f $ Pull b $ \ix -> ixf (ixb*fromIntegral b + ix)
        pwf $ \a ix -> wf a (ixb*fromIntegral b + ix)

--still wrong
trans10 w b = blockB w w b $ blockT w w . ixMap (transF w)
t10 = quickPrint (forceG .trans10 256 16) input2

block11 :: (Exp Word32 -> Exp Word32) -> Exp Word32 -> Exp Word32 -> GProgram ()
block11 f w h = do
    v <- Output (Pointer Int)
    ForAllBlocks $ \bx ->
        ForAll Nothing $ \ix ->
            SeqFor h $ \ixs -> do
                let i = bx*(BlockDim X)+ix+ixs*w
                let val = (Index (v,[f i])) :: Exp Int
                Assign v i val


trans11 :: Exp Word32 -> GProgram ()
trans11 w = block11 (transF w) w w
t11 = quickPrint trans11 256



block12 :: (Exp Word32 -> Exp Word32) -> Exp Word32 -> Exp Word32 -> GProgram ()
block12 f w h = do
    v <- Output (Pointer Int)
    ForAllBlocks $ \bx -> do
        ForAll Nothing $ \ix -> do
            gid <- return (bx*(BlockDim X)+ix)
            SeqFor h $ \ixs -> do
                let i = gid+ixs*w
                let val = (Index (v,[f i])) :: Exp Int
                Assign v i val

trans12 :: Exp Word32 -> GProgram ()
trans12 w = block12 (transF w) w w
t12 = quickPrint trans12 256

map13 :: (Scalar a) => ((Exp Word32 -> Exp a -> TProgram ()) -> Exp Word32 -> Program Thread ()) -> GProgram ()
map13 p = do
    v <- Output (Pointer Int)
    ForAllBlocks $ \bx -> do
        ForAll Nothing $ \ix -> do
            let gid = bx*(BlockDim X)+ix
            p (Assign v) gid


block13 :: (Scalar a) => (Exp Word32 -> Exp Word32) -> Exp Word32 -> Exp Word32 -> GlobPull (Exp a) -> GProgram ()

block13 f w h p = map13 $ \wif gid ->
            SeqFor h $ \ixs -> do
                let i = gid+ixs*w
                let val = p ! (f i)
                wif i val

trans13 :: (Scalar a) => Exp Word32 -> GlobPull (Exp a) -> GProgram ()
trans13 w p = block13 (transF w) w w p
t13 = quickPrint (trans13 256) input2



mapGid2 :: (APull a -> BProgram (APull b))
        -> GlobPull a
        -> GlobPush b
mapGid2 f (GlobPull ixf)  =
  GlobPush
    $ \wf ->
      ForAllBlocks
       $ \bix ->
         do -- BProgram do block 
           let n = BlockDim X --kkkk
           let pully = APull n ixf --this n is wrong
           res <- f pully
           ForAll Nothing $ \ix ->
             wf (res ! (bix * BlockDim X + ix)) (bix * BlockDim X + ix)


data APull a = APull (Exp Word32) (Exp Word32 -> a)

instance Indexible APull a where
  access (APull n ixf) = ixf

instance IxMap APull where
  ixMap f (APull n ixf) = APull n (ixf.f)

trans14 :: Exp Word32 -> APull a -> APull a
trans14 w arr = ixMap (transF w) arr
t14 = quickPrint (forceG.mapGid2 (return . trans14 256)) input2

forceA :: APull a -> APull a
forceA = undefined

trans15 :: Exp Word32 -> APull a -> APull a
trans15 w = forceA . ixMap (transF w)
t15 = quickPrint (forceG.mapGid2 (return . trans15 256)) input2


instance IxMap GlobPull where
  ixMap f (GlobPull ixf) = GlobPull (ixf.f)

trans16 :: Exp Word32 -> GlobPull a -> GlobPush a
trans16 w = pushGN 256 16.(ixMap (transF w))
t16 = quickPrint (forceG . trans16 256) input2

