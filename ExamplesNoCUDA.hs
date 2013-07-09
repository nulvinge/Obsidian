module ExamplesNoCuda where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian

import Data.Word
import Data.Int
import Data.Bits

import qualified Data.Vector.Storable as V

import Control.Monad.State
import Debug.Trace
import Obsidian.AddOn.Analysis

import Prelude hiding (zipWith,sum,replicate,take,drop)
import qualified Prelude as P 

---------------------------------------------------------------------------
-- Util 
---------------------------------------------------------------------------
quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 
 
---------------------------------------------------------------------------
-- MapFusion example
---------------------------------------------------------------------------

mapFusion :: Pull Word32 EInt -> BProgram (Pull Word32 EInt)
mapFusion arr =
  do
    imm <- force $ (fmap (+1) . fmap (*2)) arr
    force $ (fmap (+3) . fmap (*4)) imm

splitUp :: (ASize l, Num l)
           => l -> Pull (Exp Word32) a -> Pull (Exp Word32) (Pull l a)
splitUp n (Pull m ixf) = Pull (m `div` fromIntegral n) $ 
                          \i -> Pull n $ \j -> ixf (i * (sizeConv n) + j)


splitUpS :: Word32 -> Pull Word32 a -> Pull Word32 (Pull Word32 a)
splitUpS n (Pull m ixf) = Pull (m `div` n) $ 
                          \i -> Pull n $ \j -> ixf (i * (fromIntegral n) + j)

coalesce :: Word32 -> Pull Word32 a -> Pull Word32 (Pull Word32 a)
coalesce n arr =
  Pull s $ \i ->
    Pull n $ \j -> arr ! (i + (fromIntegral s) * j)
  where s = (len arr) `div` n

--test1 :: Pull (Exp Word32) EInt -> GProgram (Push Grid (Exp Word32) EInt)
--test1 input = liftG  $ fmap mapFusion (splitUp 256 input) 

input1 :: Pull (Exp Word32) EInt 
input1 = namedGlobal "apa" (variable "X")

test :: Pull EWord32 EInt -> GProgram ()
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
         => (a -> a -> a) -> Pull Word32 a -> BProgram (Pull Word32 a)
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
histogram :: Pull EWord32 EInt32 -> GProgram ()
histogram arr = do
  global <- Output $ Pointer Word32
  forAllT (len arr) $ \gix -> atomicOp global (i32ToW32 (arr ! gix)) AtomicInc

  
atomicOp n e1 a = AtomicOp n e1 a >> return () 

getHist =
  quickPrint histogram
             ((undefinedGlobal (variable "X") :: Pull (Exp Word32) EInt32) :- ())
  
reconstruct :: Pull EWord32 EWord32 -> Push Grid EWord32 EInt32
reconstruct arr = Push (len arr) f
  where
    f k = do forAllT (len arr) $ \gix ->
               let startIx = arr ! gix
               in  SeqFor (arr ! (gix+1) - startIx) $ \ix ->
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

testFold4 :: Pull EWord32 EWord32 -> Program Grid ()
testFold4 = join . liftM forceG . liftG . testFold3 

flatten :: ASize l => Pull EWord32 (Pull l a) -> Pull EWord32 a
flatten pp =
  Pull (n*m) $ \ix -> (pp ! (ix `div` m)) ! (ix `mod` m)  
  where 
    n = len pp
    m = sizeConv (len (pp ! 0))
  
inputFold :: Pull Word32 EWord32 
inputFold = namedPull "apa" 256 

inputF :: Pull EWord32 EWord32 
inputF = namedPull "apa" (variable "X") 


-- reverseglobal 
revG :: Pull EWord32 a -> Pull EWord32 a
revG arr = mkPullArray n $ \ix -> arr ! (sizeConv n - 1 - ix)
 where
   n = len arr

testRev :: Scalar a=>  Pull EWord32 (Exp a) -> GProgram () 
testRev = forceG . push Grid . revG
-} 
   
---------------------------------------------------------------------------
-- Simple 
---------------------------------------------------------------------------

s1 :: ( Num a, MemoryOps a) =>
     Pull Word32 a -> BProgram (Pull Word32 a)
s1 arr = do
  a1 <- force (fmap (+3) arr)
  a2 <- force (fmap (+2) a1) 
  force (fmap (+1) a2)  

--gs1 :: (Num a, MemoryOps a) =>
--     Pull EWord32 a -> Program Grid (Push Grid EWord32 a)
--gs1 = liftG . (fmap s1) . splitUp 256 


--getgs1 =
--  quickPrint (join . liftM forceG . gs1)
--             (undefinedGlobal (variable "X") :: Pull (EWord32) EWord32)


---------------------------------------------------------------------------
-- Matrix Mul
---------------------------------------------------------------------------

type SMatrix a = Pull Word32 (Pull Word32 a)

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
    where pushNG :: ASize s => Word32 -> Pull s e -> Push Grid s e
          pushNG = pushN
          l = len (a!0)

input2 :: Pull (Word32) EInt
input2 = namedGlobal "apa" (1024*16)

tt0 = quickPrint (joinPushNG . transpose . splitUpS 16) (input2 :- ())


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
          -> Pull l (Pull Word32 a1) -> Program Grid (Push Grid l1 a1)    
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
          => SMatrix a -> SMatrix a -> Program Grid (Push Grid Word32 a)    
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
--          => SMatrix a -> SMatrix a -> Push Grid Word32 a
{- 
matMul :: (Num c, MemoryOps c)
          => SPull (SPull c)
          -> SPull (SPull c) -> SPush Grid c
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


 {- 
matMulIn  a b = matMul (toMatrix 256 256 a) (toMatrix 256 256 b)


toMatrix :: Word32 -> Word32 -> Pull Word32 a -> SMatrix a 
toMatrix n m arr = Pull n $ \i -> Pull m $ \j -> arr ! (i * (sizeConv m) + j)


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

incP :: DPull EFloat -> DPush Grid EFloat
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


convToPush :: SPull a -> SPush Block a
convToPush arr =
  Push n $ \wf ->
   forAll (fromIntegral n) $ \tid -> wf (arr ! tid) tid
  where
    n = len arr                             


red1 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> BProgram (SPush Block a)
red1 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = do
        let (a1,a2) = evenOdds arr
        arr' <- unsafeForce $ zipWith f a1 a2
        red1 f arr'

red2 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> BProgram (SPush Block a)
red2 f arr
    | len arr == 1 = return $ push arr
    | otherwise    = do
        let (a1,a2) = halve arr
        arr' <- unsafeForce $ zipWith f a1 a2
        red2 f arr'

red3 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> BProgram (SPush Block a)
red3 f arr
    | len arr == 2 = return $ push $ singleton $ f (arr!0) (arr!1)
    | otherwise    = do
        let (a1,a2) = halve arr
        arr' <- unsafeForce $ zipWith f a1 a2
        red3 f arr'

red4 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> BProgram (SPush Block a)
red4 f arr = do
    arr' <- force $ pConcatMap (return . seqReduce f)
                               (splitUpS 8 arr)
    red3 f arr'

red5 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> BProgram (SPush Block a)
red5 f arr = do
    arr' <- force $ pConcatMap (return . seqReduce f)
                               (coalesce 8 arr)
    red3 f arr'

red6 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> BProgram (SPush Block a)
red6 f arr = do
    arr' <- force $ pConcatMap (return . seqReduce f)
                               (coalesce 16 arr)
    red3 f arr'

red7 :: MemoryOps a
     => (a -> a -> a)
     -> SPull a
     -> BProgram (SPush Block a)
red7 f arr = do
    arr' <- force $ pConcatMap (return . seqReduce f)
                               (coalesce 32 arr)
    red3 f arr'

tr1 = printAnalysis ((pConcatMap $ red1 (+)) . splitUpS 1024) (input2 :- ())
tr2 = printAnalysis ((pConcatMap $ red2 (+)) . splitUpS 1024) (input2 :- ())
tr3 = printAnalysis ((pConcatMap $ red3 (+)) . splitUpS 1024) (input2 :- ())
tr4 = printAnalysis ((pConcatMap $ red4 (+)) . splitUpS 1024) (input2 :- ())
tr5 = printAnalysis ((pConcatMap $ red5 (+)) . splitUpS 1024) (input2 :- ())
tr6 = printAnalysis ((pConcatMap $ red6 (+)) . splitUpS 1024) (input2 :- ())
tr7 = printAnalysis ((pConcatMap $ red7 (+)) . splitUpS 1024) (input2 :- ())

err5 :: (MemoryOps a, Num a) => SPull a -> BProgram (SPush Block a)
err5 arr = do
  arr' <- force $ pConcatMap (return . seqReduce (+) . ixMap (+1))
                             (splitUpS 8 arr)
  arr'' <- force $ Push (len arr') $ \wf ->
            ForAll (fromIntegral $ len arr') $ \i -> wf 0 0 >> f (flip wf $ i) i (arr'!i)
  err3 arr''
  where 
    --f :: (Num a, MemoryOps a) => Exp Word32 -> Exp a -> TProgram ()
    f wf i a = ifThenElse ((i .&. 1) ==* 0)
                  (wf a)
                  (wf (-a))
    --f i a b = ifThenElse ((i .&. 1) ==* 0) (return $ a+b) (return $ b+a)

err3 :: (MemoryOps a, Num a) => SPull a -> BProgram (SPush Block a)
err3 arr
    | len arr == 2 = return $ push $ singleton $ (arr!0) + (arr!1)
    | otherwise    = do
        let (a1,a2) = evenOdds arr
        arr' <- unsafeForce $ zipWith (+) a1 a2
        err3 arr'

te5 = printAnalysis ((pConcatMap $ err5) . splitUpS 1024) (input2 :- ())

reverseL :: SPull a -> BProgram (SPush Block a)
reverseL = liftM push . return . Obsidian.reverse


reverseL' :: MemoryOps a => SPull a -> BProgram (SPush Block a)
reverseL' = liftM push . force . Obsidian.reverse

reverses :: DPull a -> DPush Grid a
reverses = pConcatMap reverseL . splitUp 256

largeReverse :: DPull a -> DPush Grid a
largeReverse = pConcat . Obsidian.reverse . pMap reverseL . splitUp 256

trevl  = printAnalysis ((pConcatMap $ reverseL)  . splitUpS 1024) (input2 :- ())
trevl' = printAnalysis ((pConcatMap $ reverseL') . splitUpS 1024) (input2 :- ())
trevs  = printAnalysis reverses (input1 :- ())
trevL  = printAnalysis largeReverse (input1 :- ())

mandel :: Push Grid Word32 EWord8
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

    iters :: EWord32 -> EWord32 -> TProgram (SPush Thread EWord8)
    iters bid tid = return $ fmap extract $ seqUntil (f bid tid) cond (0,0,1)
    extract (_,_,c) = ((w32ToW8 c) `mod` 16) * 16

    genRect bs ts p = generate bs (return . generate ts . p)

tm0 = printAnalysis mandel ()

sklansky :: (Choice a, MemoryOps a)
         => Int -> (a -> a -> a) -> SPull a -> BProgram (SPush Block a)
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

ts1 = printAnalysis ((pConcatMap $ sklansky 10 (+)) . splitUpS 1024) (input2 :- ())

phase :: Choice a
      => Int -> (a -> a -> a) -> SPull a -> SPush Block a
phase i f arr =
  Push l $ \wf -> ForAll s12 $ \tid -> do
    let ix1 = tid .&. (bit i) .|. (tid .&. (complement $ bit i) `shiftL` 1)  -- iinsertZero i tid
        ix2 = complementBit ix1 i
        ix3 = ix2 .&. (complement $ bit i - 1) - 1
    wf (arr ! ix1) ix1
    wf (f (arr ! ix3) (arr ! ix2)) ix2
  where
    l = len arr
    l2 = l `div` 2
    s12 = sizeConv l2


compose :: MemoryOps a
        => [SPull a -> SPush Block a]
        -> SPull a -> BProgram (SPush Block a)
compose [f] arr    = return $ f arr
compose (f:fs) arr = do
  arr2 <- force $ f arr
  compose fs arr2


sklansky2 :: (Choice a, MemoryOps a)
          => Int -> (a -> a -> a) -> SPull a -> BProgram (SPush Block a)
sklansky2 n op = compose [phase i op | i <- [0..(n-1)]]

ts2 = printAnalysis ((pConcatMap $ sklansky2 10 (+)) . splitUpS 1024) (input2 :- ())

sklansky3 :: (Choice a, MemoryOps a)
          => Int -> (a -> a -> a) -> SPull a -> BProgram (SPush Block a)
sklansky3 n op arr = do
  im <- force $ load 2 arr
  compose [phase i op | i <- [0..(n-1)]] im

ts3 = printAnalysis ((pConcatMap $ sklansky3 10 (+)) . splitUpS 1024) (input2 :- ())

load :: ASize l => Word32 -> Pull l a -> Push Block l a 
load n arr =
  Push m $ \wf ->
    forAll (sizeConv n') $ \tid ->
      seqFor (fromIntegral n) $ \ix -> 
        wf (arr ! (tid + (ix*n'))) (tid + (ix*n')) 
  where
    m = len arr
    n' = sizeConv m `div` fromIntegral n

