
{-# LANGUAGE ScopedTypeVariables,
             GADTs,
             RankNTypes,
             ExistentialQuantification,
             MultiParamTypeClasses,
             FlexibleInstances,
             TypeFamilies,
             TypeOperators,
             Arrows,
             ImpredicativeTypes,
             FlexibleContexts #-}

module ArrowExamples where

import Obsidian.Exp
import Obsidian.Array
import Obsidian.Library
import Debug.Trace

import Data.Word
import Data.Bits

import Control.Category
import Control.Arrow
import Control.Arrow.ApplyUtils
import Control.Monad

import Arrow
import ArrowLib

import Prelude hiding (zipWith,sum,replicate,id,(.))
import qualified Prelude as P


testInput :: Pull Word32 (Exp Int)
testInput = namedGlobal "apa" 2048

testInput' :: Pull (Exp Word32) (Exp Int)
testInput' = namedGlobal "apa" 2048

testInputS :: Pull Word32 (Exp Float)
testInputS = namedGlobal "apa" 512

testInputW :: Pull Word32 (Exp Word32)
testInputW = namedGlobal "apa" 512

liftE a = resize (fromIntegral (len a)) a

reduce0 :: (Scalar a, Num (Exp a)) => Word32 -> (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce0 1 = id
reduce0 n = (uncurry (zipWith (+)) <<< halve)
       ^>> aSync
       >>> reduce0 (n`div`2)
tr0 = quickPrint t testInput
  where s a = liftG $ simpleRun (reduce0 (len a)) a
        t a = run 1024 (reduce0 (len a)) a 

reduce1 :: (Scalar a, Num (Exp a)) => Word32 -> (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce1 n = (uncurry (zipWith (+)) <<< halve)
       ^>> if n == 2
        then id
        else aSync
         >>> reduce1 (n`div`2)
tr1 = quickPrint t testInput
  where t a = run 1024 (reduce1 (len a)) a 

reduce2 :: (Scalar a, Num (Exp a)) => (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce2 = proc a -> do
      rec a' <- Pure (halve >>> uncurry (zipWith (+))) -< a
          b <- aSync -< a'
          a <- id -< if len a == 1 then b else b
      returnA -< a
tr2 = quickPrint s testInput
  where s a = liftG $ simpleRun reduce2 a
        t a = run 1024 reduce2 a

appl :: ArrowApply a => a b c -> a b c
appl a = proc b -> do app -< (a,b)


reduce3 :: (Scalar a, Num (Exp a)) => (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce3 = proc a -> do
      let b = uncurry (zipWith (+)) $ halve a
      app -< (if len b == 1 then id else reduce3 <<< aSync,b)
tr3 = quickPrint t testInput
  where s a = liftG $ simpleRun reduce3 a
        t a = run 1024 reduce3 a

reduce4 :: (Scalar a, Num (Exp a)) => Pull Word32 (Exp a) :~> (Pull Word32 (Exp a))
reduce4 a = do
  let b = uncurry (zipWith (+)) $ halve a
  if len b == 1
    then return b
    else (mSync >=> reduce4) b
tr4 = quickPrint t testInput
  where s a = liftG $ simpleRun (monadicA reduce4) a
        t a = run 1024 (monadicA reduce4) a

rreduce4 :: (Scalar a, Num (Exp a)) => Word32 -> Pull Word32 (Exp a) :~> (Pull Word32 (Exp a))
rreduce4 m a = do
  let b = uncurry (zipWith (+)) $ evenOddParts m a
  if m == 1
    then return b
    else do b' <- mSync b
            rreduce4 (m`div`2) b
trr4 = quickPrint t testInput
  where s a = liftG $ simpleRun (monadicA (rreduce4 (len a`div`2))) a
        t a = run 1024 (monadicA (rreduce4 (len a`div`2))) a


bitonicMerge0 :: (Scalar a, Ord (Exp a)) => ((Pull Word32 (Exp a),Word32) :-> Pull Word32 (Exp a))
bitonicMerge0 = proc (a,s) -> do
  let s' = fromIntegral s
      b = Pull (len a) $ \i -> If (i .&. s' ==* 0)
                                  (mine (a!i) (a!(i `xor` s')))
                                  (maxe (a!i) (a!(i `xor` s')))
  app -< (if s == 1 then arr fst else bitonicMerge0 <<< first aSync,(b,s`div`2))
bitonic0 :: (Scalar a, Ord (Exp a)) => Pull Word32 (Exp a) :-> Pull Word32 (Exp a)
bitonic0 = proc a -> do
  bitonicMerge0 -< (a,len a`div`2)
tb0 = quickPrint t testInputS
  where s a = liftG $ simpleRun bitonic0 a
        t a = run 512 bitonic0 a

bitonicMerge1 :: (Scalar a, Ord (Exp a)) => Word32 -> Word32 -> (Pull Word32 (Exp a) :~> Pull Word32 (Exp a))
bitonicMerge1 s m a = do
  let s' = fromIntegral s
      m' = fromIntegral m
      b = Pull (len a) $ \i -> If ((i .&. s' ==* 0) /=* (i .&. m' ==* 0))
                                  (mine (a!i) (a!(i `xor` s')))
                                  (maxe (a!i) (a!(i `xor` s')))
  if s <= 1
    then return b
    else do b' <- mSync b
            bitonicMerge1 (s`div`2) m b'
bitonicSort1 :: (Scalar a, Ord a) => Pull Word32 (Exp a) :~> Pull Word32 (Exp a)
bitonicSort1 a = f 2 a
  where f m a | m >= len a = return a
        f m a              = do b <- bitonicMerge1 m (2*m) a
                                f (m*2) b
tb1 = quickPrint t testInputS
  where s a = liftG $ simpleRun (monadicA bitonicSort1) a
        t a = run 512 (monadicA bitonicSort1) a

sctfftR1 :: Word32 -> Pull Word32 (Exp Float, Exp Float) :~> Pull Word32 (Exp Float, Exp Float)
sctfftR1 s c = if s <= 1 then return c else do
  a <- sctfftR1 (s`div`2) c
  let sf :: (Floating (Exp a)) => (Exp a)
      sf = fromRational $ toRational s
      sw = fromIntegral s
      b = Pull (len a) $ \i ->
        let k = i .&. (2*sw)
            twiddle = expi(-1*pi / (2*sf) * (word32ToFloat k))
            expi x = (cos x, sin x)
            (ar,ai) `mul` (br,bi) = (ar*br-ai*bi, ar*bi + ai*br)
            (ar,ai) `add` (br,bi) = (ar+br, ai+bi)
            (ar,ai) `sub` (br,bi) = (ar-br, ai-bi)
        in ifp (i .&. sw ==* 0)
            ((a!i) `add` (twiddle `mul` (a!(i `xor` sw))))
            ((a!i) `sub` (twiddle `mul` (a!(i `xor` sw))))
  if s == len c`div`2
    then return b
    else arrSync2 b
sctfft1 :: Pull Word32 (Exp Float) :~> Pull Word32 (Exp Float)
sctfft1 a = do
  let b = fmap (\x -> (x,0)) a
  c <- sctfftR1 (len b`div`2) b
  return $ fmap fst c
tf1 = quickPrint t testInputS
  where s a = liftG $ simpleRun (monadicA sctfft1) a
        t a = run 512 (monadicA sctfft1) a


listScan0 :: (a ~ Word32) => (Exp (Word32) -> Exp Bool) -> (Exp a -> Exp a -> Exp a) -> Word32
          -> (PullC a, PullC Word32) :~> (PullC a)
listScan0 isNull op n (rank,next) = do
  let r = Pull (len next) $ \k ->
          let nk = next!k
          in ifp (isNull nk)
              (rank!k,next!k)
              ((rank!k) `op` (rank!nk), next!nk)
  r' <- arrSync2 r
  if strace n <= 1
    then return $ fmap fst r'
    else listScan0 isNull op (n`div`2) (unzipp r')

listRank0 :: (Exp (Word32) -> Exp Bool) -> Pull Word32 (Exp Word32) :~> Pull Word32 (Exp Word32)
listRank0 isNull nexti = do
  let ranki :: Pull Word32 (Exp Word32)
      ranki = fmap (\v -> If (isNull v) 0 1) nexti
      s = len nexti
  listScan0 isNull (+) s (ranki,nexti)
tl0 = quickPrint t testInputW
  where s a = liftG $ simpleRun (monadicA $ listRank0 p) a
        t a = run 1024 (monadicA $ listRank0 p) a
        p v = v ==* 0

sortList0 :: (Exp (Word32) -> Exp Bool) -> PullC2 Word32 Word32 :~> PullC Word32
sortList0 p a = do
  let (next,vals) = unzipp a
  rank <- listRank0 p next
  return $ ixMap (rank!) vals
ts0 = quickPrint t input
  where s a = liftG $ simpleRun (monadicA $ sortList0 p) a
        t a = run 1024 (monadicA $ sortList0 p) a
        input = zipp (testInputW,testInputW)
        p v = v ==* 0

constructTour0 :: PullC2 Word32 Word32 :~> PullC Word32
constructTour0 a = do
  b <- mSync $ interleave (merge a) (merge $ (fmap (\(a,b) -> (b,a))) a)
  c <- bitonicSort1 b
  return $ c
  where merge :: PullC2 Word32 Word32 -> PullC Word32
        merge arr   = fmap (\(a,b) -> a*elen arr+b) arr
        unmerge arr = fmap (\a -> a`divMod`elen arr) arr
tt0 = quickPrint t input
  where s a = liftG $ simpleRun (monadicA $ constructTour0) a
        t a = run 1024 (monadicA $ constructTour0) a
        input = zipp (testInputW,testInputW)
        p v = v ==* 0



