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

data Stage a where
  IXMap :: (Exp Word32 -> Exp Word32) -> Stage a
  FMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> Word32 -> Word32 -> Stage a
  Comp  :: Stage a -> Stage a -> Stage a
  Id    :: Stage a
  Len   :: (Word32 -> Stage a) -> Stage a

(>>>) = Comp
infixr 9 >>>

instance Show (Stage a) where
  show (IXMap f) = "IXMap f"
  show (FMap f n n') = "FMap f " ++ show n ++ " " ++ show n'
  show (Comp a b) = "(" ++ show a ++ " >> " ++ show b ++ ")"
  show (Id) = "Id"
  show (Len f) = "Len f"


--(>-) :: Stage a b -> Stage a b -> Stage a b
--(IXMap f) >- (IXMap f') = IXMap (f.f')
--(FMap f) >- (FMap f') = FMap (f.f')
--a >- b = a `Comp` b

opt :: Word32 -> Stage a -> Stage a
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

runG :: (Scalar a)
     => Stage a -> Word32 -> Word32
     -> GlobPull (Exp a) -> GProgram (GlobPull (Exp a))
runG (IXMap f `Comp` s) b nn a = runG s b nn (ixMap f a)
runG (Len f) b nn a = runG (f nn) b nn a
runG (Id) b nn a = return a
runG ss b nn (GlobPull ixf) = do
    as <- rf
    runG tn b tl as
  where rf = cheat $ forceG $ GlobPush $ \wf -> do
                ForAllBlocks $ \bix -> do
                    Push _ pf <- runB tr b nn bix (Pull nn ixf)
                    pf wf
        (tr, tn, tl) = strace $ runBable ss b nn

strace a = trace (show a) a

runBable :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32)
runBable (a `Comp` as) b nn = case a of
    (FMap f n n') -> (a `Comp` tr, tn, tl)
                where (tr,tn,tl) = runBable as b ((nn`div`n)*n')
    (IXMap f) | nn < b -> (a `Comp` tr, tn, tl)
                where (tr,tn,tl) = runBable as b nn
    _             -> (Id, (a `Comp` as), nn)
runBable (Len f) b nn = runBable (f nn) b nn
runBable s b nn = (Id,s,nn)

runB :: (Scalar a)
     => Stage a -> Word32 -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
runB (s `Comp` Id) b nn bix a = runB s b nn bix a
runB (IXMap f `Comp` ss) b nn bix a = runB ss b nn bix (ixMap f a)
runB (s `Comp` ss) b nn bix a = do
        a' <- runB s b nn bix a
        a'' <- force a'
        runB ss b (len a'') bix a''
runB (FMap f n n') b nn bix a = return rf
    where rf = Push (nn `div` n*n') $ \wf ->
                    ForAll (Just (nn`div`n)) $ \tix -> do
                        let ix = (bix*(fromIntegral (nn`div`n))+tix)*(fromIntegral n)
                            l = [a ! (ix+fromIntegral six) | six <- [0..n-1]]
                            fl = f l
                        sequence_ [wf (fl !! (fromIntegral six)) (ix+fromIntegral six) | six <- [0..n'-1]]
runB Id b nn bix a = return (push a)
--runB s b nn a = (return (),s)

quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

reduce :: (Scalar a, Num (Exp a)) => Stage a
reduce = Len (\l ->
   if l==1 then Id
           else IXMap (\i -> i`div`2 + (fromIntegral l)`div`2*(i `mod` 2))
            >>> FMap (\[a,b] -> [a+b]) 2 1
            >>> reduce
   )

testInput :: GlobPull (Exp Int)
testInput = namedGlobal "apa"
tr0 = quickPrint (runG reduce 1024 1024) testInput

