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
  FMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> [Exp Word32 -> Exp Word32] -> Word32 -> Stage a
  Comp  :: Stage a -> Stage a -> Stage a
  Id    :: Stage a
  Len   :: (Word32 -> Stage a) -> Stage a

(>>>) = Comp
infixr 9 >>>

instance Show (Stage a) where
  show (FMap f i o) = "FMap f " ++ show (length i) ++ " " ++ show o
  show (Comp a b) = "(" ++ show a ++ " >> " ++ show b ++ ")"
  show (Id) = "Id"
  show (Len f) = "Len f"

--(>-) :: Stage a b -> Stage a b -> Stage a b
--(IXMap f) >- (IXMap f') = IXMap (f.f')
--(FMap f) >- (FMap f') = FMap (f.f')
--a >- b = a `Comp` b

opt :: Word32 -> Stage a -> Stage a
--opt m ((IXMap f) `Comp` (IXMap f') `Comp` b) = opt m $ IXMap (f'.f) `Comp` b
--opt m ((FMap f i o) `Comp` (FMap f2 i2 o2) `Comp` b) | o == fromIntegral (length i2) =
--        opt m $ FMap (f2.f) i o2 `Comp` b
--opt m ((IXMap f'') `Comp` (FMap f n n') `Comp` (FMap f2 n2 n2') `Comp` b) | n' == n2 =
--        opt m $ IXMap f'' `Comp` FMap (f2.f) n n' `Comp` b
opt m (FMap f i o `Comp` a) = FMap f i o `Comp` opt ((m `div` fromIntegral (length i))*o) a
--opt m (IXMap f `Comp` a) = IXMap f `Comp` opt m a
opt m (Id `Comp` a) = opt m a
opt m (a `Comp` Id) = opt m a
opt m a = a


--a >- b = a `Comp` b

segment :: Int -> [a] -> [[a]]
segment = undefined

runG :: (Scalar a)
     => Stage a -> Word32 -> Word32
     -> GlobPull (Exp a) -> GProgram (GlobPull (Exp a))
--runG (IXMap f `Comp` s) b nn a = runG s b nn (ixMap f a)
runG (Len f) b nn a = runG (f nn) b nn a
runG (Id) b nn a = return a
runG ss b nn (GlobPull ixf) = do
    as <- rf
    runG tn b tl as
  where rf = cheat $ forceG $ GlobPush $ \wf -> do
                ForAllBlocks $ \bix -> do
                    Push _ pf <- runB tr b nn bix (Pull nn ixf)
                    pf wf
        (tr, tn, tl) = runBable ss b nn

strace a = trace (show a) a

blockAccess ixf = False

runBable :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32)
runBable (a@(FMap f i o) `Comp` as) b nn = (tr1 `Comp` tr2, tn2, tl2)
      where (tr1,Id,tl1) = runBable' a b nn
            (tr2,tn2,tl2) = runBable' as b tl1
runBable a b nn = runBable' a b nn

runBable' :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32)
runBable' (a@(FMap f i o) `Comp` as) b nn =
    if nn < b || all blockAccess i
        then (tr1 `Comp` tr2, tn2, tl2)
        else (Id, (a `Comp` as), nn)
      where (tr1,Id,tl1) = runBable' a b nn
            (tr2,tn2,tl2) = runBable' as b tl1
runBable' a@(FMap f i o) b nn = (a,Id,nn `div` fromIntegral (length i) * o)
runBable' (Len f) b nn = runBable (f nn) b nn
runBable' s b nn = (Id,s,nn)

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
    where (tr, tn, tl) = strace $ runWable s b nn
runB s b nn bix a = runW s b nn bix a

warpAccess ixf = False

runWable :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32)
runWable (a@(FMap f i o) `Comp` as) b nn = (tr1 `Comp` tr2, tn2, tl2)
      where (tr1,Id,tl1) = runWable' a b nn
            (tr2,tn2,tl2) = runWable' as b tl1
runWable a b nn = runWable' a b nn

runWable' :: (Scalar a)
         => Stage a -> Word32 -> Word32
         -> (Stage a, Stage a, Word32)
runWable' (a@(FMap f i o) `Comp` as) b nn =
    if nn <= 32 || all warpAccess i
        then (tr1 `Comp` tr2, tn2, tl2)
        else (Id, (a `Comp` as), nn)
      where (tr1,Id,tl1) = runWable' a b nn
            (tr2,tn2,tl2) = runWable' as b tl1
runWable' a@(FMap f i o) b nn = (a,Id,nn `div` fromIntegral (length i) * o)
runWable' (Len f) b nn = runWable (f nn) b nn
runWable' s b nn = (Id,s,nn)


runW :: (Scalar a)
     => Stage a -> Word32 -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
runW (s `Comp` Id) b nn bix a = runW s b nn bix a
runW (s `Comp` ss) b nn bix a = do
        a' <- runW s b nn bix a
        a'' <- write a'
        runW ss b (len a'') bix a''
runW (FMap f i o) b nn bix a = return rf
    where rf = Push (newn * o) $ \wf ->
                    ForAll (Just newn) $ \tix -> do
                        let ix = (bix*(fromIntegral newn)+tix)
                            l = map (\ixf -> a!(ixf ix)) i
                            fl = f l
                        sequence_ [wf (fl !! (fromIntegral six)) (ix*(fromIntegral o)+fromIntegral six) | six <- [0..o-1]]
          ni = fromIntegral (length i)
          newn = nn `div` ni
runW Id b nn bix a = return (push a)




quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

reduce :: (Scalar a, Num (Exp a)) => Stage a
reduce = Len (\l ->
   if l==1 then Id
           else FMap (\[a,b] -> [a+b]) [id, (+(fromIntegral l`div`2))] 1
            >>> reduce
   )

testInput :: GlobPull (Exp Int)
testInput = namedGlobal "apa"
tr0 = quickPrint (runG reduce 1024 1024) testInput

