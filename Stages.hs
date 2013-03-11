{-# LANGUAGE ScopedTypeVariables,
             GADTs,
             RankNTypes,
             ExistentialQuantification,
             FlexibleContexts #-}

module Stages where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian.Program hiding (Bind,Return)
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Array
import Obsidian.Library
import Obsidian.Force
import Obsidian.CodeGen.InOut
import Obsidian.Atomic
import Debug.Trace

import Data.Word
import Data.Int
import Data.Bits
import Data.Maybe (isJust)
import Data.List (genericIndex)

import qualified Data.Vector.Storable as V

import Control.Monad.State

import Prelude hiding (zipWith,sum,replicate)
import qualified Prelude as P

data Array a = Arr [a]

type Index = Exp Word32 -> Exp Word32

data BackStage a where
  FMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> [Index] -> [Index] -> [Index] -> Word32 -> BackStage a

type Stage a = [BackStage a]

data FrontStage a b where
  SFMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> [Index] -> [Index] -> FrontStage a ()
  Bind   :: FrontStage a b -> (b -> FrontStage a c) -> FrontStage a c
  Return :: b -> FrontStage a b
  Len    :: FrontStage a Word32
  Block  :: FrontStage a Word32

instance Monad (FrontStage a) where
  return = Return
  (>>=)  = Bind

run :: (Scalar a)
    => FrontStage a () -> Word32 -> Word32
    -> GlobPull (Exp a) -> GProgram (GlobPull (Exp a))
run a b n = runG s' b n
  where (s,_,_,()) = mkStage b n [] a
        s' = opt s

mkStage :: (Scalar a)
        => Word32 -> Word32 -> [Index] -> FrontStage a b
        -> (Stage a, [Index], Word32, b)
mkStage _ 0 _ _ = error "Stage cannot have zero width"
mkStage 0 _ _ _ = error "Stage cannot have zero blocksize"
mkStage b n ob (SFMap f i o) = ([FMap f i o ob n], o, ni ,())
  where ni = n `div` fromIntegral (length i) * fromIntegral (length o)
mkStage b n ob (a `Bind` f) = (s1 ++ s2, ob2, n2, b2)
  where (s1,ob1,n1,b1) = mkStage b n ob a
        (s2,ob2,n2,b2) = mkStage b n1 ob1 (f b1)
mkStage b n ob (Return a)   = ([],ob,n,a)
mkStage b n ob (Len)        = ([],ob,n,n)
mkStage b n ob (Block)      = ([],ob,n,b)

instance Show (BackStage a) where
  show (FMap f i o ob nn) = "FMap f " ++ show (length i) ++ " " ++ show (length o) ++  " " ++ show (length ob)
  --show (Len f) = "Len f"

--(>-) :: Stage a b -> Stage a b -> Stage a b
--(IXMap f) >- (IXMap f') = IXMap (f.f')
--(FMap f) >- (FMap f') = FMap (f.f')
--a >- b = a `Comp` b

opt :: Stage a -> Stage a
opt a = a


--a >- b = a `Comp` b

accessA :: Word32 -> [Index] -> Word32 -> [Index] -> Bool
accessA divisions ob n i = (length arrWriteThreads) == (length arrReadThreads)
                        && all sameDivision (zip arrWriteThreads arrReadThreads)
  where arrWriteThreads = getIndices ob
        arrReadThreads  = getIndices i
        getIndices :: [Index] -> [Exp Word32]
        getIndices ixf = concat [[(ixf !! x) (fromIntegral ix)
                                 | x <- [0..(length ixf-1)]]
                                | ix <- [0..((n `div` (fromIntegral (length ixf)))-1)]]
        sameDivision (wt,rt) = isJust $ do
          w <- getConstant wt
          r <- getConstant rt
          guard $ (w `div` divisions) == (r `div` divisions)
        getConstant (Literal a) = Just a

runable :: (Scalar a)
        => Word32
        -> Stage a -> Word32
        -> (Stage a, Stage a, Word32, Word32)
runable divisions (a:as) b = 
  case runable' (a:as) of
    ([],_,_,_) -> ([tr1], as, tl1, tt1)
      where ([tr1],[],tl1,tt1) = single a
    a          -> a
  where runable' :: (Scalar a)
                 => Stage a
                 -> (Stage a, Stage a, Word32, Word32)
        runable' ao@(a@(FMap f i o ob nn) : as) =
            if null ob || {- nn <= divisions || -} accessA divisions ob nn i
                then case as of
                    [] -> single a
                    _  -> (tr1 : tr2, tn2, tl2, tt1 `max` tt2)
                else ([], ao, nn, 0)
            where ([tr1],[], tl1,tt1)  = single a
                  (tr2,tn2,tl2,tt2) = runable' as
        --runable' s = ([],s,undefined,undefined)
        single a@(FMap f i o ob nn) = ([a], [], nn`div`ni*no, nn`div`ni)
            where ni = fromIntegral (length i)
                  no = fromIntegral (length o)


runG :: (Scalar a)
     => Stage a -> Word32 -> Word32
     -> GlobPull (Exp a) -> GProgram (GlobPull (Exp a))
--runG (IXMap f `Comp` s) b nn a = runG s b nn (ixMap f a)
--runG (Len f) b nn a = runG (f nn) b nn a
runG [] _ _ a = return a
runG ss b nn (GlobPull ixf) = do
    as <- rf
    runG tn b tl as
  where rf = cheat $ forceG $ GlobPush $ \wf -> do
                ForAllBlocks $ \bix -> do
                    Push _ pf <- runB tr b bix (Pull nn ixf)
                    pf wf
        (tr, tn, tl, _) = runBable ss b

runBable :: (Scalar a)
         => Stage a -> Word32
         -> (Stage a, Stage a, Word32, Word32)
runBable a b = runable b a b

runB :: (Scalar a)
     => Stage a -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
--runB (IXMap f `Comp` ss) b nn bix a = runB ss b nn bix (ixMap f a)
runB s b bix a = do
        a' <- runW tr b bix a
        case tn of
          [] -> return a'
          _  -> do a'' <- force a'
                   runB tn b bix a''
    where (tr, tn, _, _) = runWable s b
--runB s b bix a = runW s b bix a

runWable :: (Scalar a)
         => Stage a -> Word32
         -> (Stage a, Stage a, Word32, Word32)
runWable a b = runable 32 a b

runW :: (Scalar a)
     => Stage a -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
--runW (s `Comp` ss) b nn bix a = do
--        a' <- runW s b nn bix a
--        a'' <- write a'
--        runW ss b (len a'') bix a''
runW s b bix a = do
    case tn of
        [] -> return a'
        _  -> do a'' <- write a'
                 runW tn b bix a''
    where a' = Push tl $ \wf ->
                    ForAll (Just tt) $ \tix -> do
                        let ix = (bix*(fromIntegral b)+tix)
                        runT tr b ix wf a
          (tr, tn, tl, tt) = runTable s b

runTable :: (Scalar a)
         => Stage a -> Word32
         -> (Stage a, Stage a, Word32, Word32)
runTable = runable 1

runT :: (Scalar a)
     => Stage a -> Word32 -> Exp Word32
     -> (Exp a -> Exp Word32 -> TProgram ())
     -> Pull (Exp a) -> TProgram ()
runT [FMap f i o ob nn] b ix wf a = sequence_ [wf (fl !! (fromIntegral six))
                                            (ix*(fromIntegral (length o))+fromIntegral six)
                                        | six <- [0..(length o)-1]]
    where l = map (\ixf -> a!(ixf ix)) i
          fl = f l
runT [] b ix wf a = return ()

quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

strace a = trace (show a) a


reduce :: (Scalar a, Num (Exp a)) => FrontStage a ()
reduce = do
  l <- Len
  if l==1
    then Return ()
    else do SFMap (\[a,b] -> [a+b]) [id, (+(fromIntegral l`div`2))] [id]
            reduce

--class SFMappable a
--  sfmap :: a -> FrontStage b ()

--sfmap (uncurry (+)) (id, (+l`div`2))

testInput :: GlobPull (Exp Int)
testInput = namedGlobal "apa"
tr0 = quickPrint (run reduce 1024 2048) testInput

tr1 = mkStage 1024 1024 [id] (reduce :: FrontStage Int ())
tr2 = opt $ fst4 $ mkStage 1024 1024 [id] (reduce :: FrontStage Int ())

fst4 (a,_,_,_) = a
