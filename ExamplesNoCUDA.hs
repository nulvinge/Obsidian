{-# LANGUAGE FlexibleContexts #-}
module ExamplesNoCUDA where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian

import Data.Word
import Data.Int
import Data.Bits

import qualified Data.Vector.Storable as V

import Control.Monad.State
import Debug.Trace
import Obsidian.Dependency.Analysis
import Obsidian.Inplace
import Obsidian.Num

import Prelude hiding (zipWith,sum,replicate,take,drop)
import qualified Prelude as P 


inputSF :: SPull EFloat
inputSF = namedGlobal "apa" (1024*16)

inputSD :: SPull EDouble
inputSD = namedGlobal "apa" (1024*16)

inputSI :: Pull (Word32) EInt
inputSI = namedGlobal "apa" (1024*16)

inputDI :: Pull (Exp Word32) EInt 
inputDI = namedGlobal "apa" (variable "X")

inputMI :: Pull (Exp Word32) EInt 
inputMI = namedGlobal "apa" (1024*variable "X")

---------------------------------------------------------------------------
-- Util 
---------------------------------------------------------------------------
quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 
 
---------------------------------------------------------------------------
-- MapFusion example
---------------------------------------------------------------------------

mapFusion :: Pull Word32 EInt -> Program (Pull Word32 EInt)
mapFusion arr =
  do
    imm <- force $ fmap (+1) $ fmap (*2) arr
    force $ fmap (+3) $ fmap (*4) imm

splitUpD :: (ASize l, Num l)
           => l -> Pull (Exp Word32) a -> Pull (Exp Word32) (Pull l a)
splitUpD n (Pull m ixf) = Pull (m `div` fromIntegral n) $ 
                          \i -> Pull n $ \j -> ixf (i * (sizeConv n) + j)

splitUpS :: Word32 -> Pull Word32 a -> Pull Word32 (Pull Word32 a)
splitUpS n (Pull m ixf) = Pull (m `div` n) $ 
                          \i -> Pull n $ \j -> ixf (i * (fromIntegral n) + j)

--test1 :: Pull (Exp Word32) EInt -> Program (Push (Exp Word32) EInt)
--test1 input = liftG  $ fmap mapFusion (splitUp 256 input) 

test :: Pull EWord32 EInt -> Program ()
test a = do
  Comment "test"
  return ()

---------------------------------------------------------------------------
-- Scans 
---------------------------------------------------------------------------
{-
sklansky :: (Choice a, MemoryOps a)
            => Int
            -> (a -> a -> a)
            -> Pull Word32 a
            -> BProgram (Pull Word32 a)
sklansky 0 op arr = return arr
sklansky n op arr =
  do 
    let arr1 = binSplit (n-1) (fan op) arr
    arr2 <- force arr1
    sklansky (n-1) op arr2

-- fan :: (Choice a, ASize l) => (a -> a -> a) -> Pull l a -> Pull l a
fan :: Choice a => (a -> a -> a) -> SPull a -> SPull a
fan op arr =  a1 `conc`  fmap (op c) a2 
    where 
      (a1,a2) = halve arr
      c = a1 ! sizeConv (len a1 - 1)

sklanskyG logbs op arr =
  mapG (sklansky logbs op) (splitUp (2^logbs) arr)

getSklansky =
  quickPrint (sklanskyG 8 (+))
             ((undefined :: Pull (Exp Word32) EInt32) :- ())
-} 
---------------------------------------------------------------------------
-- kStone (TEST THAT THIS IS REALLY A SCAN!) 
---------------------------------------------------------------------------
{- 
kStone :: (Choice a, MemoryOps a) 
          => Int -> (a -> a -> a) -> Pull Word32 a -> BProgram (Pull Word32 a)
kStone 0 op arr = return arr
kStone n op arr =
  do
    res <- kStone (n-1) op arr 
    let r1  = drop (2^(n-1)) res
        r1' = take (2^(n-1)) res 
        r2 = zipWith op res r1 
    force (r1' `conc` r2) 

-- Push array version 
kStoneP :: (Choice a, MemoryOps a) 
          => Int -> (a -> a -> a) -> Pull Word32 a -> BProgram (Pull Word32 a)
kStoneP 0 op arr = return arr
kStoneP n op arr =
  do
    res <- kStoneP (n-1) op arr 
    let r1  = drop (2^(n-1)) res
        r1' = take (2^(n-1)) res 
        r2 = zipWith op res r1 
    force (concP Block r1' r2) 
 
-} 

--kStoneG logbs op =
--join . liftM forceG . liftG . fmap (kStone logbs op) . splitUp (2^logbs)
--kStonePG logbs op =
--  join . liftM forceG . liftG . fmap (kStoneP logbs op) . splitUp (2^logbs) 

--getKStone =
--  quickPrint (kStoneG 8 (+))
--             (undefinedGlobal (variable "X") :: Pull (Exp Word32) EInt32)

--getKStoneP =
--  quickPrint (kStonePG 8 (+))
--             (undefinedGlobal (variable "X") :: Pull (Exp Word32) EInt32)

---------------------------------------------------------------------------
-- Brent Kung
--------------------------------------------------------------------------- 
bKung :: (Choice a, MemoryOps a) 
         => (a -> a -> a) -> Pull Word32 a -> Program (Pull Word32 a)
bKung op arr | len arr == 1 = return arr
bKung op arr = undefined 


--bKungG op =
--  join . liftM forceG . liftG . fmap (bKung op) . splitUp 256

--getBKung =
--  quickPrint (bKungG (+))
--             (undefinedGlobal (variable "X") :: Pull (Exp Word32) EInt32)


---------------------------------------------------------------------------
-- Go Towards Counting sort again.  
--------------------------------------------------------------------------- 
histogram :: Pull EWord32 EInt32 -> Program ()
histogram arr = do
  global <- Output $ Pointer Word32
  forAll (len arr) $ \gix -> atomicOp global (i32ToW32 (arr ! gix)) AtomicInc

  
atomicOp n e1 a = AtomicOp n e1 a >> return () 

getHist =
  quickPrint histogram
             ((undefinedGlobal (variable "X") :: Pull (Exp Word32) EInt32) :- ())
  
reconstruct :: Pull EWord32 EWord32 -> Push EWord32 EInt32
reconstruct arr = Push (len arr) f
  where
    f k = do forAll (len arr) $ \gix ->
               let startIx = arr ! gix
               in  seqFor (arr ! (gix+1) - startIx) $ \ix ->
                   do 
                     k (w32ToI32 gix) (ix + startIx)
                 
getRec =
  quickPrint reconstruct
             ((undefinedGlobal (variable "X") :: Pull (EWord32) EWord32) :- ())


---------------------------------------------------------------------------
-- Testing some sequential loop approaches
---------------------------------------------------------------------------

{- 
testFold :: Pull Word32 EWord32 -> Pull Word32 (Program Thread EWord32)
testFold arr = fmap (seqFold (+) 0) (splitUpS (32 :: Word32)  arr)

testFold2 :: Pull Word32 EWord32 -> BProgram (Pull Word32 EWord32)
testFold2 = liftB . testFold

testFold3 :: Pull EWord32 EWord32
             -> Pull EWord32 (BProgram (Pull Word32 EWord32))
testFold3 arr =  fmap (testFold2) (splitUp 256 arr)

testFold4 :: Pull EWord32 EWord32 -> Program ()
testFold4 = join . liftM forceG . liftG . testFold3 

flatten :: ASize l => Pull EWord32 (Pull l a) -> Pull EWord32 a
flatten pp =
  Pull (n*m) $ \ix -> (pp ! (ix `div` m)) ! (ix `mod` m)  
  where 
    n = len pp
    m = sizeConv (len (pp ! 0))
  
inputSFold :: Pull Word32 EWord32 
inputSFold = namedPull "apa" 256 


-- reverseglobal 
revG :: Pull EWord32 a -> Pull EWord32 a
revG arr = mkPullArray n $ \ix -> arr ! (sizeConv n - 1 - ix)
 where
   n = len arr

testRev :: Scalar a=>  Pull EWord32 (Exp a) -> Program () 
testRev = forceG . push . revG
-} 
   
---------------------------------------------------------------------------
-- Simple 
---------------------------------------------------------------------------

s1 :: ( Num a, MemoryOps a) =>
     Pull Word32 a -> Program (Pull Word32 a)
s1 arr = do
  a1 <- force (fmap (+3) arr)
  a2 <- force (fmap (+2) a1) 
  force (fmap (+1) a2)  

--gs1 :: (Num a, MemoryOps a) =>
--     Pull EWord32 a -> Program (Push EWord32 a)
--gs1 = liftG . (fmap s1) . splitUp 256 


--getgs1 =
--  quickPrint (join . liftM forceG . gs1)
--             (undefinedGlobal (variable "X") :: Pull (EWord32) EWord32)


---------------------------------------------------------------------------
-- Matrix Mul
---------------------------------------------------------------------------

{-
transpose0 :: (ASize l1, ASize l2) => Pull l1 (Pull l2 a) -> Pull l2 (Pull l1 a)
transpose0 arr = mkPullArray m
                $ \i -> mkPullArray n
                       $ \j -> (arr ! j) ! i                                       
                                
   where
     n = len arr
     m = len (arr ! 0)
-}

strace a = trace (show a) a

joinM :: (ASize l) => Pull l (Pull l a) -> Pull l a
joinM a = mkPullArray n $ \i -> (a!(i`div`m))!(i`mod`m) --(a!(i`div`m)) ! (i`mod`m)
    where m = sizeConv $ len (a!0)
          n = len (a!0)*(len a)

joinPushNG a = pushNG l $ joinM a
    where pushNG :: ASize s => Word32 -> Pull s e -> Push s e
          pushNG = pushN
          l = len (a!0)

tt0 = quickPrint (joinPushNG . transpose . splitUpS 16) (inputSI :- ())


transpose :: SMatrix a -> SMatrix a
transpose arr = mkPullArray m
                $ \i -> mkPullArray n
                       $ \j -> (arr ! j) ! i                                       
                                
   where
     n = len arr
     m = len (arr ! 0) 



{-      
matMul :: (Num a1, ASize l1, ASize l, MemoryOps a1, LiftB a1)
          => Pull l1 (Pull l a1)
          -> Pull l (Pull Word32 a1) -> Program (Push l1 a1)    
matMul x y = liftG
             -- Pull l (BProgram (Pull l EFloat))  
             $ fmap liftB
             -- Pull l (Pull l (Program Thread EFloat))
             $ mkPullArray n
             $ \i -> mkPullArray m
                     $ \j -> cell i j 
                          
  where cell i j = seqFold (+) 0 $ zipWith (*) (x ! i) (y' ! j) 
        y' = transpose y
        n  = len x
        m  = len y'
-} 

mkMatrix n m f = mkPullArray n $ \i -> mkPullArray m $ \j -> f i j 

{-
matMul :: (Num a, MemoryOps a, LiftB a)
          => SMatrix a -> SMatrix a -> Program (Push Word32 a)    
matMul x y = liftG
             -- :: Pull l (BProgram (Pull l a))  
             $ fmap liftB
             -- :: Pull l (Pull l (Program Thread a))
             $ mkMatrix n m cell 
                          
  where cell i j = seqFold (+) 0 $ zipWith (*) (x ! i) (y' ! j) 
        y' = transpose y
        n  = len x
        m  = len y'
-} 

--matMul2 :: Num a 
--          => SMatrix a -> SMatrix a -> Push Word32 a
{- 
matMul :: (Num c, MemoryOps c)
          => SPull (SPull c)
          -> SPull (SPull c) -> SPush c
matMul x y = zipWithG body (replicate n x) (replicate m (transpose y))
  where
    n = len x
    m = len (y ! 0) 
    body a b = force (zipWithT cell a b)
    cell i j = do
      let arr = zipWith (*) i j 
      r <- seqReduce (+) arr
      return (singleton r) 
-}               
--  where cell i j = seqFold (+) 0 $ zipWith (*) (x ! i) (y' ! j) 
--        y' = transpose y
--        n  = len x
--        m  = len y'


matMulIn  a b = matMul (toMatrix 256 256 a) (toMatrix 256 256 b)


toMatrix :: Word32 -> Word32 -> Pull Word32 a -> SMatrix a 
toMatrix n m arr = Pull n $ \i -> Pull m $ \j -> arr ! (i * (sizeConv m) + j)


{- 
getMM =
  quickPrint matMulIn
             ((undefinedGlobal (256*256) {-(variable "X")-} :: Pull Word32 EFloat) :-
              (undefinedGlobal (256*256) {-(variable "Y")-} :: Pull Word32 EFloat) :- ())

-} 
{-
getMM2 =
  quickPrint matMulIn2
             ((undefinedGlobal (256*256) {-(variable "X")-} :: Pull Word32 EFloat) :->
              (undefinedGlobal (256*256) {-(variable "Y")-} :: Pull Word32 EFloat))
-}

{- 
inc :: SPull EFloat -> SPull EFloat
inc  = fmap (+1)

getIncP = putStrLn $ genKernel "incP" incP (input :- ())

input :: DPull EFloat
input = namedGlobal "apa" (variable "X")

incP :: DPull EFloat -> DPush EFloat
incP arr = mapG (return . inc) ((splitUp 512 . ixMap (vperm2 12 3 1. vperm 11 1 0)) arr)


swapBitBlocks :: Int -> Int -> Int -> Exp Word32 -> Exp Word32
swapBitBlocks l m r i = f .|. (lbs `shiftR` (m-r)) .|. (rbs `shiftL` (l-m))
  where
    f = i .&. complement (oneBitsFT r l)
    lbs = i .&. (oneBitsFT m l) 
    rbs = i .&. (oneBitsFT r m)

oneBitsFT :: Int -> Int -> Exp Word32
oneBitsFT i j = (1 `shiftL` j)  - (1 `shiftL` i)

-- r > 0   xor the bit at r-1 with all bits in the block from r to l
bitBlockXor :: Int -> Int -> Exp Word32 -> Exp Word32
bitBlockXor l r i = i `xor` (((b `shiftL` (l-r)) - b)`shiftL` 1)
  where 
    b = i .&. (1 `shiftL` r)

vperm l m r = bitBlockXor (l-1) (r+l-m-1) . swapBitBlocks l m r

vperm2 l m r = swapBitBlocks l (r+l-m) r . bitBlockXor (l-1) (r+l-m-1)
-} 


convToPush :: SPull a -> SPush a
convToPush arr =
  Push n $ \wf ->
   forAll (fromIntegral n) $ \tid -> wf (arr ! tid) tid
  where
    n = len arr                             


red1 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red1 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = do
        let (a1,a2) = evenOdds arr
        arr' <- unsafeForce $ zipWith f a1 a2
        red1 f arr'

red2 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red2 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = do
        let (a1,a2) = halve arr
        arr' <- unsafeForce $ zipWith f a1 a2
        red2 f arr'

red3 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red3 f arr
    | len arr == 2 = return $ push $ singleton $ f (arr!0) (arr!1)
    | otherwise    = do
        let (a1,a2) = halve arr
        arr' <- unsafeForce $ zipWith f a1 a2
        red3 f arr'

red4 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red4 f arr = do
    arr' <- force $ pConcatMap (seqReduce f)
                               (splitUpS 8 arr)
    red3 f arr'

red5 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red5 f arr = do
    arr' <- force $ pConcatMap (seqReduce f)
                               (coalesce 8 arr)
    red3 f arr'

red6 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red6 f arr = do
    arr' <- force $ pConcatMap (seqReduce f)
                               (coalesce 16 arr)
    red3 f arr'

red7 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red7 f arr = do
    arr' <- force $ pConcatMap (seqReduce f)
                               (coalesce 32 arr)
    red3 f arr'


red10 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red10 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = do
        let (a1,a2) = halve arr
        arr' <- force $ pushA [(Par,Thread,128)] $ zipWith f a1 a2
        red10 f arr'

red11 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red11 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = do
        let (a1,a2) = halve arr
        arr' <- force $ pushA [(Par,Thread,128),(Par,Vector,0)] $ zipWith f a1 a2
        red11 f arr'

red12 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red12 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = do
        let (a1,a2) = halve arr
        arr' <- force $ pushA [(Par,Thread,128),(Seq,Thread,0)] $ zipWith f a1 a2
        red12 f arr'

red13 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> Program (SPush a)
red13 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = WithStrategy [(Par,Thread,128),(Seq,Thread,0)] $ do
        let (a1,a2) = halve arr
        arr' <- force $ zipWith f a1 a2
        red13 f arr'

redl0 :: (MemoryOps a, Precise a)
     => (Log a -> Log a -> Log a)
     -> SPull a
     -> Program (SPush a)
redl0 f a = do
  a' <- red10 f $ fmap toLog a
  return $ fmap fromLog a'

redc0 :: (MemoryOps a, Compensable a)
     => (Compensated a -> Compensated a -> Compensated a)
     -> SPull a
     -> Program (SPush a)
redc0 f a = do
  a' <- red10 f $ fmap toCompensated a
  return $ fmap fromCompensated a'

tr1 = printAnalysis (pSplitMapJoin 1024 $ red1 (+)) (inputSI :- ())
tr2 = printAnalysis (pSplitMapJoin 1024 $ red2 (+)) (inputSI :- ())
tr3 = printAnalysis (pSplitMapJoin 1024 $ red3 (+)) (inputSI :- ())
tr4 = printAnalysis (pSplitMapJoin 1024 $ red4 (+)) (inputSI :- ())
tr5 = printAnalysis (pSplitMapJoin 1024 $ red5 (+)) (inputSI :- ())
tr6 = printAnalysis (pSplitMapJoin 1024 $ red6 (+)) (inputSI :- ())
tr7 = printAnalysis (pSplitMapJoin 1024 $ red7 (+)) (inputSI :- ())
tr10= printAnalysis (pSplitMapJoin 1024 $ red10(+)) (inputSI :- ())
tr11= printAnalysis (pSplitMapJoin 1024 $ red11(+)) (inputSI :- ())
tr12= printAnalysis (pSplitMapJoin 1024 $ red12(+)) (inputSI :- ())
tr13= printAnalysis (pSplitMapJoin 1024 $ red13(+)) (inputSI :- ())
trl0= printAnalysis (pSplitMapJoin 1024 $ redl0(*)) (inputSF :- ())
trc0= printAnalysis (pSplitMapJoin 1024 $ redc0(+)) (inputSF :- ())
trc1= printAnalysis (pSplitMapJoin 1024 $ redc0(*)) (inputSF :- ())


or4 = printPrg $ do
  let a@(Push n p) = (pConcatMapJoin $ red4 (+)) $ splitUpS 1024 inputSI
  output <- outputArray a
  p (\a ix -> assignArray output a ix)

err5 :: (MemoryOps a, Num a) => SPull a -> Program (SPush a)
err5 arr = do
  arr' <- force $ pConcatMap (seqReduce (+) . ixMap (+1))
                             (splitUpS 8 arr)
  arr'' <- force $ Push (len arr') $ \wf ->
            forAll (fromIntegral $ len arr') $ \i -> wf 0 0 >> f (flip wf $ i) i (arr'!i)
  err3 arr''
  where 
    --f :: (Num a, MemoryOps a) => Exp Word32 -> Exp a -> Program ()
    f wf i a = ifThenElse ((i .&. 1) ==* 0)
                  (wf a)
                  (wf (-a))
    --f i a b = ifThenElse ((i .&. 1) ==* 0) (return $ a+b) (return $ b+a)

err3 :: (MemoryOps a, Num a) => SPull a -> Program (SPush a)
err3 arr
    | len arr == 2 = return $ push $ singleton $ (arr!0) + (arr!1)
    | otherwise    = do
        let (a1,a2) = evenOdds arr
        arr' <- unsafeForce $ zipWith (+) a1 a2
        err3 arr'

te5 = printAnalysis ((pConcatMapJoin $ err5) . splitUpS 1024) (inputSI :- ())

reverseL :: SPull a -> Program (SPush a)
reverseL = liftM push . return . Obsidian.reverse


reverseL' :: MemoryOps a => SPull a -> Program (SPush a)
reverseL' = liftM push . force . Obsidian.reverse

reverses :: DPull a -> DPush a
reverses = pConcatMapJoin reverseL . splitUp 1024

largeReverse1 :: DPull a -> DPush a
largeReverse1 = pConcat . Obsidian.reverse . pMapJoin reverseL . splitUp 1024

largeReverse2 :: DPull a -> DPush a
largeReverse2 = pConcatMapJoin reverseL . Obsidian.reverse . splitUp 1024

largeReverse3 :: DPull a -> DPush a
largeReverse3 = pConcat . Obsidian.reverse . fmap (pJoin.reverseL) . splitUp 1024

trevl  = printAnalysis ((pConcatMapJoin $ reverseL)  . splitUpS 1024) (inputSI :- ())
trevl' = printAnalysis ((pConcatMapJoin $ reverseL') . splitUpS 1024) (inputSI :- ())
trevs  = printAnalysis reverses (inputDI :- ())
trevL1 = printAnalysis largeReverse1 (inputDI :- ())
trevL2 = printAnalysis largeReverse2 (inputDI :- ())
trevL3 = printAnalysis largeReverse3 (inputDI :- ())

mandel :: Push Word32 EWord8
mandel = genRect 512 512 iters
  where
    xmax =  1.2 :: EFloat
    xmin = -2.0 :: EFloat
    ymax =  1.2 :: EFloat
    ymin = -1.2 :: EFloat

    deltaP = (xmax - xmin) / 512.0
    deltaQ = (ymax - ymin) / 512.0

    f bid tid (x,y,iter) =
        (x*x - y*y + (xmin + (w32ToF tid) * deltaP)
        ,2*x*y + (ymax - (w32ToF bid) * deltaQ)
        ,iter+1)

    cond (x,y,iter) = ((x*x + y*y) <* 4) &&* iter <* 512

    iters :: EWord32 -> EWord32 -> SPush EWord8
    iters bid tid = fmap extract $ seqUntil (f bid tid) cond (0,0,1)
    extract (_,_,c) = ((w32ToW8 c) `mod` 16) * 16

    genRect bs ts p = generate bs (generate ts . p)

tm0 = printAnalysis mandel ()

sklansky :: (Choice a, MemoryOps a)
         => Int -> (a -> a -> a) -> SPull a -> Program (SPush a)
sklansky 0 op arr = return $ push arr
sklansky n op arr = do
  let arr1 = binSplit (n-1) (fan op) arr
  arr2 <- force arr1
  sklansky (n-1) op arr2

  where
    fan :: Choice a
        => (a -> a -> a) -> SPull a -> SPull a
    fan op arr = a1 `conc` fmap (op c) a2
      where (a1,a2) = halve arr
            c = a1 ! fromIntegral (len a1-1)

ts1 = printAnalysis ((pConcatMapJoin $ sklansky 10 (+)) . splitUpS 1024) (inputSI :- ())

phase :: Choice a
      => Int -> (a -> a -> a) -> SPull a -> SPush a
phase i f arr =
  Push l $ \wf -> forAll s12 $ \tid -> do
    let ix1 = tid .&. (bit i -1) .|. ((tid .&. (complement $ bit i - 1)) <<* 1)  -- iinsertZero i tid
        ix2 = complementBit ix1 i
        ix3 = ix2 .&. (complement $ bit i - 1) -- - 1

    let i0 = (tid `mod` (bit i))
        i3 = (tid - i0)
        i1 = i0 + i3
        i2 = complementBit i1 i

    wf (arr ! ix1) ix1
    wf (f (arr ! ix3) (arr ! ix2)) ix2

    --wf (arr ! i1) i1
    --wf (f (arr ! i3) (arr ! i2)) i2
  where
    l = len arr
    l2 = l `div` 2
    s12 = sizeConv l2


compose :: MemoryOps a
        => [SPull a -> SPush a]
        -> SPull a -> Program (SPush a)
compose [f] arr    = return $ f arr
compose (f:fs) arr = do
  arr2 <- force $ f arr
  compose fs arr2


sklansky2 :: (Choice a, MemoryOps a)
          => Int -> (a -> a -> a) -> SPull a -> Program (SPush a)
sklansky2 n op = compose [phase i op | i <- [0..(n-1)]]

ts2 = printAnalysis ((pConcatMapJoin $ sklansky2 10 (+)) . splitUpS 1024) (inputSI :- ())

sklansky3 :: (Choice a, MemoryOps a)
          => Int -> (a -> a -> a) -> SPull a -> Program (SPush a)
sklansky3 n op arr = do
  im <- force $ load 2 arr
  compose [phase i op | i <- [0..(n-1)]] im

load :: ASize l => Word32 -> Pull l a -> Push l a 
load n arr =
  Push m $ \wf ->
    forAll (sizeConv n') $ \tid ->
      seqFor (fromIntegral n) $ \ix -> 
        wf (arr ! (tid + (ix*n'))) (tid + (ix*n')) 
  where
    m = len arr
    n' = sizeConv m `div` fromIntegral n

ts3 = printAnalysis ((pConcatMapJoin $ sklansky3 10 (+)) . splitUpS 1024) (inputSI :- ())

scan1 :: (MemoryOps a) => (a -> a -> a) -> Pull Word32 a -> Program (Pull Word32 a)
scan1 f a = do a' <- forceInplace (push a)
               scan1' f 1 a'
               return $ pullInplace a'

scan1' :: (MemoryOps a) => (a -> a -> a) -> Word32 -> Inplace Word32 a -> Program ()
scan1' f s' a = do
  let s = sizeConv s'
      al :: Word32
      al = fromIntegral $ len a
  when (s' < len a) $ do
    inplaceForce a $ pusha (len a) (al`div`(s'*2)) $ \wf i -> do
      let j = 2*s*i+2*s-1
      wf j $ (a!j) `f` (a!(j-s))
  when (s'*2 < len a) $ do
    scan1' f (s'*2) a
    inplaceForce a $ pusha (len a) (al`div`(s'*2)-1) $ \wf i -> do
      let j = 2*s*i+2*s-1
      wf j $ (a!(j+s)) `f` (a!j)

ts4 = printAnalysis ((pConcatMap $ pJoinPush . scan1 (+)) . splitUpS 1024) (inputSI :- ())

matMul a b = pConcatMapJoin (matMulRow (transpose b)) a
  where matMulRow mat row = return $ pConcatMapJoin (dotP row) mat
        dotP a b = return
                 $ seqReduce (+)
                 $ zipWith (*) a b

tmm0 = printAnalysis matMulIn
             ((undefinedGlobal (256*256) {-(variable "X")-} :: Pull Word32 EFloat) :-
              (undefinedGlobal (256*256) {-(variable "Y")-} :: Pull Word32 EFloat) :- ())

saxpy0 :: (Num a, ASize l)
       => a -> Pull l a -> Pull l a -> Push l a
saxpy0 a x y = pConcatMap (push . fmap (\(x,y) -> y+a*x))
                          (splitUp 256 $ zipp (x,y))

saxpy1 :: (Num a, ASize l)
       => a -> Pull l a -> Pull l a -> Push l a
saxpy1 a x y = pConcatMap (pConcatMap (seqMap (\(x,y) -> y+a*x)) . splitUp 8)
                          (splitUp (8*256) $ zipp (x,y))

--this is wrong
saxpy2 :: (Num a, ASize l, MemoryOps a)
       => a -> Pull l a -> Pull l a -> Push l a
saxpy2 a x y = pConcatMap (pConcatMap(seqMap (\(x,y) -> y+a*x)) . coalesce 8)
                          (splitUp (8*256) $ zipp (x,y))

saxpy3 :: (Num a, ASize l, MemoryOps a)
       => a -> Pull l a -> Pull l a -> Push l a
saxpy3 a x y = pConcatMap (pUnCoalesceMap (seqMap (\(x,y) -> y+a*x)) . coalesce 8)
                          (splitUp (8*256) $ zipp (x,y))

saxpy4 :: (Num a, ASize l, MemoryOps a)
       => a -> Pull l a -> Pull l a -> Push l a
saxpy4 a x y = pSplitMap (8*256) (pCoalesceMap 8 (seqMap (\(x,y) -> y+a*x)))
             $ zipp (x,y)

saxpy5 :: (Num a, ASize l)
       => a -> Pull l a -> Pull l a -> Push l a
saxpy5 a x y = pushA [(Par,Thread,256),(Seq,Thread,2),(Par,Block,0)]
             $ fmap (\(x,y) -> y+a*x) $ zipp (x,y)

saxpy6 :: (Num a, ASize l)
       => a -> Pull l a -> Pull l a -> Push l a
saxpy6 a x y = push $ fmap (\(x,y) -> y+a*x) $ zipp (x,y)

tsx0  = printAnalysis saxpy0 (2 :- inputSI :- inputSI :- ())
tsx0D = printAnalysis saxpy0 (2 :- inputDI :- inputDI :- ())
tsx1  = printAnalysis saxpy1 (2 :- inputSI :- inputSI :- ())
tsx1D = printAnalysis saxpy1 (2 :- inputDI :- inputDI :- ())
tsx2  = printAnalysis saxpy2 (2 :- inputSI :- inputSI :- ())
tsx2D = printAnalysis saxpy2 (2 :- inputDI :- inputDI :- ())
tsx3  = printAnalysis saxpy3 (2 :- inputSI :- inputSI :- ())
tsx3D = printAnalysis saxpy3 (2 :- inputDI :- inputDI :- ())
tsx4  = printAnalysis saxpy4 (2 :- inputSI :- inputSI :- ())
tsx4D = printAnalysis saxpy4 (2 :- inputDI :- inputDI :- ())
tsx5  = printAnalysis saxpy5 (2 :- inputSI :- inputSI :- ())
tsx5D = printAnalysis saxpy5 (2 :- inputDI :- inputDI :- ())
tsx5M = printAnalysis saxpy5 (2 :- inputMI :- inputMI :- ())
tsx6  = printAnalysis saxpy6 (2 :- inputSI :- inputSI :- ())
tsx6D = printAnalysis saxpy6 (2 :- inputDI :- inputDI :- ())
tsx6M = printAnalysis saxpy6 (2 :- inputMI :- inputMI :- ())

bitonicMerge1 :: (MemoryOps a, OrdE a) => Word32 -> Word32 -> Pull Word32 a -> Program (Push Word32 a)
bitonicMerge1 s m a = do
  let s' = fromIntegral s
      m' = fromIntegral m
      b = pusha (len a) (len a) $ \wf i -> ifThenElse ((i .&. s' ==* 0) /=* (i .&. m' ==* 0))
                                  (wf i (minE (a!i) (a!(i `xor` s'))))
                                  (wf i (maxE (a!i) (a!(i `xor` s'))))
  if s <= 1
    then return b
    else do b' <- force b
            bitonicMerge1 (s`div`2) m b'

bitonicSort1 :: (MemoryOps a, OrdE a) => Pull Word32 a -> Program (Pull Word32 a)
bitonicSort1 a = f 2 a
  where f m a | m >= len a = return a
        f m a              = do b <- bitonicMerge1 m (2*m) a
                                b' <- force b
                                f (m*2) b'

tb1 = printAnalysis ((pConcatMapJoin $ liftM push . bitonicSort1) . splitUpS 256) (inputSI :- ())

