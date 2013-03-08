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

import qualified Data.Vector.Storable as V

import Control.Monad.State

import Prelude hiding (zipWith,sum,replicate)
import qualified Prelude as P

data Array a = Arr [a]

data Stage a where
  FMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> [Exp Word32 -> Exp Word32] -> Word32 -> Stage a
  Comp  :: Stage a -> Stage a -> Stage a
  Id    :: Stage a

data FrontStage a b where
  SFMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> [Exp Word32 -> Exp Word32] -> Word32 -> FrontStage a ()
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
  where (s,_,()) = mkStage b n a
        s' = opt n s

mkStage :: (Scalar a)
        => Word32 -> Word32 -> FrontStage a b
        -> (Stage a, Word32, b)
mkStage b n (SFMap f i o) = (FMap f i o, ni ,())
  where ni = n `div` (fromIntegral (length i)) * o
mkStage b n (a `Bind` f) = (s1 `Comp` s2, n2, b2)
  where (s1,n1,b1) = mkStage b n a
        (s2,n2,b2) = mkStage b n1 (f b1)
mkStage b n (Return a) = (Id,n,a)
mkStage b n (Len) = (Id,n,n)
mkStage b n (Block) = (Id,n,b)

instance Show (Stage a) where
  show (FMap f i o) = "FMap f " ++ show (length i) ++ " " ++ show o
  show (Comp a b) = "(" ++ show a ++ " >> " ++ show b ++ ")"
  show (Id) = "Id"
  --show (Len f) = "Len f"

--(>-) :: Stage a b -> Stage a b -> Stage a b
--(IXMap f) >- (IXMap f') = IXMap (f.f')
--(FMap f) >- (FMap f') = FMap (f.f')
--a >- b = a `Comp` b

opt :: Word32 -> Stage a -> Stage a
opt 0 _ = error "Stage cannot have zero width"
opt m (FMap f i o `Comp` a) = FMap f i o `Comp` opt ((m `div` fromIntegral (length i))*o) a
opt m (Id `Comp` a) = opt m a
opt m (a `Comp` Id) = opt m a
opt m a = a


--a >- b = a `Comp` b

runable :: (Scalar a)
        => Word32 -> ((Exp Word32 -> Exp Word32) -> Bool)
        -> Stage a -> Word32 -> Word32
        -> (Stage a, Stage a, Word32, Word32)
runable max access aa b nn = 
  case aa of
    (a@(FMap f i o) `Comp` as) -> (tr1 `Comp` tr2, tn2, tl2, ti1)
            where (tr1,Id,tl1,ti1) = runable' a nn
                  (tr2,tn2,tl2,_)  = runable' as tl1
    _                          -> runable' aa nn
  where runable' :: (Scalar a)
                 => Stage a -> Word32
                 -> (Stage a, Stage a, Word32, Word32)
        runable' (a@(FMap f i o) `Comp` as) nn =
                if nn <= max || all access i
                    then (tr1 `Comp` tr2, tn2, tl2,ti1)
                    else (Id, (a `Comp` as), nn, ti1)
                where (tr1,Id,tl1,ti1) = runable' a nn
                      (tr2,tn2,tl2,_)  = runable' as tl1
        runable' a@(FMap f i o) nn = (a, Id, nn`div`ni*o, ni)
            where ni = fromIntegral (length i)
        --runable' (Len f) nn = runable max access (f nn) b nn
        runable' s nn = (Id,s,nn,undefined)

runG :: (Scalar a)
     => Stage a -> Word32 -> Word32
     -> GlobPull (Exp a) -> GProgram (GlobPull (Exp a))
--runG (IXMap f `Comp` s) b nn a = runG s b nn (ixMap f a)
--runG (Len f) b nn a = runG (f nn) b nn a
runG (Id) b nn a = return a
runG ss b nn (GlobPull ixf) = do
    as <- rf
    runG tn b tl as
  where rf = cheat $ forceG $ GlobPush $ \wf -> do
                ForAllBlocks $ \bix -> do
                    Push _ pf <- runB tr b nn bix (Pull nn ixf)
                    pf wf
        (tr, tn, tl) = runBable ss b nn

accessB :: (Exp Word32 -> Exp Word32) -> Bool
accessB ixf = False

runBable :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32)
runBable a b nn = (tr,tn,tl)
  where (tr,tn,tl,_) = runable b accessB a b nn

runB :: (Scalar a)
     => Stage a -> Word32 -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
runB (s `Comp` Id) b nn bix a = runB s b nn bix a
--runB (IXMap f `Comp` ss) b nn bix a = runB ss b nn bix (ixMap f a)
runB s@(_ `Comp` _) b nn bix a = do
        a' <- runW tr b nn bix a
        case tn of
          Id -> return a'
          _  -> do a'' <- force a'
                   runB tn b (len a'') bix a''
    where (tr, tn, tl) = runWable s b nn
runB s b nn bix a = runW s b nn bix a

accessW :: (Exp Word32 -> Exp Word32) -> Bool
accessW ixf = False

runWable :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32)
runWable a b nn = (tr,tn,tl)
  where (tr,tn,tl,_) = runable 32 accessB a b nn

runW :: (Scalar a)
     => Stage a -> Word32 -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
runW (s `Comp` Id) b nn bix a = runW s b nn bix a
--runW (s `Comp` ss) b nn bix a = do
--        a' <- runW s b nn bix a
--        a'' <- write a'
--        runW ss b (len a'') bix a''
runW s b nn bix a = do
    case tn of
        Id -> return a'
        _  -> do a'' <- write a'
                 runW tn b (len a'') bix a''
    where a' = Push tl $ \wf ->
                    ForAll (Just newn) $ \tix -> do
                        let ix = (bix*(fromIntegral b)+tix)
                        runT tr b nn ix wf a
          (tr, tn, tl, ti) = runTable s b nn
          newn = nn `div` ti

accessT :: (Exp Word32 -> Exp Word32) -> Bool
accessT ixf = False

runTable :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32, Word32)
runTable = runable 1 accessT

runT :: (Scalar a)
     => Stage a -> Word32 -> Word32 -> Exp Word32
     -> (Exp a -> Exp Word32 -> TProgram ())
     -> Pull (Exp a) -> TProgram ()
runT (s `Comp` Id) b nn ix wf a = runT s b nn ix wf a
runT (FMap f i o) b nn ix wf a = sequence_ [wf (fl !! (fromIntegral six))
                                            (ix*(fromIntegral o)+fromIntegral six)
                                        | six <- [0..o-1]]
    where l = map (\ixf -> a!(ixf ix)) i
          fl = f l
--runT Id b nn ix wf a = return ()

quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

strace a = trace (show a) a


reduce :: (Scalar a, Num (Exp a)) => FrontStage a ()
reduce = do
  l <- Len
  if l==1
    then Return ()
    else do SFMap (\[a,b] -> [a+b]) [id, (+(fromIntegral l`div`2))] 1
            reduce

testInput :: GlobPull (Exp Int)
testInput = namedGlobal "apa"
tr0 = quickPrint (run reduce 512 2048) testInput

tr1 = mkStage 1024 1024 (reduce :: FrontStage Int ())
tr2 = opt 1024 $ fst3 $ mkStage 1024 1024 (reduce :: FrontStage Int ())

fst3 (a,_,_) = a
