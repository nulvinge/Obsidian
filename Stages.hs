{-# LANGUAGE ScopedTypeVariables,
             GADTs,
             RankNTypes,
             ExistentialQuantification,
             FlexibleContexts #-}

module Stages where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian.Program
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

data Stage a b where
  IXMap :: (Exp Word32 -> Exp Word32) -> Stage a a
  FMap  :: (Scalar b) => ([Exp a] -> [Exp b]) -> Word32 -> Word32 -> Stage a b
  Comp  :: Stage a b -> Stage b c -> Stage a c
  Id    :: Stage a a
  Len   :: (Word32 -> Stage a' b') -> Stage a' b'

instance Show (Stage a b) where
  show (IXMap f) = "IXMap f"
  show (FMap f n n') = "FMap f " ++ show n ++ show n'
  show (Comp a b) = show a ++ " >> " ++ show b
  show (Id) = "Id"
  show (Len f) = "Len f"


--(>-) :: Stage a b -> Stage a b -> Stage a b
--(IXMap f) >- (IXMap f') = IXMap (f.f')
--(FMap f) >- (FMap f') = FMap (f.f')
--a >- b = a `Comp` b

opt :: Word32 -> Stage a b -> Stage a b
opt m ((IXMap f) `Comp` (IXMap f') `Comp` b) = opt m $ IXMap (f'.f) `Comp` b
opt m ((FMap f n n') `Comp` (FMap f2 n2 n2') `Comp` b) | n' == n2 =
        opt m $ FMap (f2.f) n n' `Comp` b
opt m ((IXMap f'') `Comp` (FMap f n n') `Comp` (FMap f2 n2 n2') `Comp` b) | n' == n2 =
        opt m $ IXMap f'' `Comp` FMap (f2.f) n n' `Comp` b
opt m (FMap f n n' `Comp` a) = FMap f n n' `Comp` opt ((m `div` n)*n') a
opt m (IXMap f `Comp` a) = IXMap f `Comp` opt m a
opt m (Id `Comp` a) = opt m a
opt m (a `Comp` Id) = opt m a
opt m a = a


--a >- b = a `Comp` b

segment :: Int -> [a] -> [[a]]
segment = undefined

runG :: (Scalar a, Scalar b)
     => Stage a b -> Word32 -> Word32
     -> GlobPull (Exp a) -> GProgram (GlobPull (Exp b))
runG (IXMap f `Comp` s) b nn a = runG s b nn (ixMap f a)
runG ss b nn (GlobPull ixf) = do
    as <- rf
    runG ts b (len (ta 0)) as
  where rf = cheat $ forceG $ GlobPush $ \wf -> do
                ForAllBlocks $ \bix -> do
                    let (Push nl pf) = ta bix
                    pf wf
                    --ForAll (Just (len a')) $ \ix ->
                    --    wf (a'!ix) (fromIntegral (len a')*bix+ix)
        (ta, ts) = runB ss b nn (Pull nn ixf)
runG (Len f) b nn a = runG (f nn) b nn a
runG (Id) b nn a = return a

runB :: (Scalar a, Scalar b)
     => Stage a b -> Word32 -> Word32
     -> Pull (Exp a) -> ((Exp Word32 -> Push (Exp c), Stage c b))
runB (Comp (FMap f n n' :: Stage a c) (s :: Stage c b)) b nn a = (rf,s)
    where rf bix = Push (nn `div` n*n') $ \wf ->
                    ForAll (Just (nn`div`n)) $ \tix -> do
                        let ix = (bix*(fromIntegral (nn`div`n))+tix)*(fromIntegral n)
                            l = [a ! (ix+fromIntegral six) | six <- [0..n-1]]
                            fl = f $ trace (show l) l
                        sequence_ [wf (fl !! (fromIntegral six)) (ix+fromIntegral six) | six <- [0..n'-1]]
--runB s b nn a = (return (),s)

quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

reduce :: (Scalar a, Num (Exp a)) => Stage a a
reduce = Len (\l ->
   if l==1 then Id
           else FMap (\[a,b] -> [a+b]) 2 1 `Comp` reduce
   )

testInput :: GlobPull (Exp Int)
testInput = namedGlobal "apa"
tr0 = quickPrint (runG reduce 1024 1024) testInput

