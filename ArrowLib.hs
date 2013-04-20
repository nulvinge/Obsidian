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
             UndecidableInstances,
             FlexibleContexts #-}

module ArrowLib where

import qualified Obsidian.CodeGen.CUDA as CUDA
import Obsidian.CodeGen.InOut
import Obsidian.Program

import Obsidian.Exp
import Obsidian.Array
import Obsidian.Library
import Obsidian.Memory

import Debug.Trace

import Data.Word
import Data.Bits
import qualified Data.Text.IO as T

import Control.Category
import Control.Arrow
import Control.Monad
import Control.Arrow.ApplyUtils

import Arrow
import Inplace
import ExpAnalysis

import Prelude hiding (zipWith,sum,replicate,id,(.))
import qualified Prelude as P

mSync :: (Array p, APushable p, MemoryOps a, TraverseExp a) => p Word32 a :~> Pull Word32 a
mSync = unmonadicA aSync

type PullC a = Pull Word32 (Exp a)
type PullC2 a b = Pull Word32 (Exp a, Exp b)


concatM :: Monad m => [a -> m a] -> a -> m a
concatM fs = foldr (>=>) return fs

--bad name and semi-ugly helper
class (MemoryOps a, TraverseExp a, Choice a) => Value a

instance (MemoryOps a, TraverseExp a, Choice a) => Value a

ttrav1 :: (TraverseExp a) => a -> a
ttrav1 = id
ttrav2 :: (MemoryOps a) => a -> a
ttrav2 = id
ttrav3 :: (Choice a) => a -> a
ttrav3 = id
ttrav4 :: (Value a) => a -> a
ttrav4 = id

{-
pSync (a,b) = do
  a' <- mSync a
  b' <- mSync b
  return (a',b')
  
psSync i = do
  let (a,b) = unzipp i
  a' <- mSync a
  b' <- mSync b
  return $ zipp (a',b')

arrSync i = do
  let (a,b) = unzipp i
  s <- mSync (a`conc`b)
  return $ zipp $ halve s

arrSync2 i = do
  let (a,b) = unzipp i
  s <- mSync (interleave a b)
  return $ zipp $ evenOdds s

-}

interleave a b = Pull (len a + len b) $ \ix ->
                    If (ix .&. 1 ==* 0) (a!(ix`div`2)) (b!(ix`div`2))

evenOddParts :: ASize l => l -> Pull l a -> (Pull l a, Pull l a)
evenOddParts m' arr = (mkPullArray (n-n2) (\ix -> arr ! (2*(ix`div`m)*m + (ix`mod`m)))
                      ,mkPullArray n2     (\ix -> arr ! (2*(ix`div`m)*m + m + (ix`mod`m)))
                      )
  where n  = len arr
        n2 = n`div`2
        m = fromIntegral m'

type a :~> b = a -> ArrowAsMonad (Arrow.:->) b

liftE a = resize (fromIntegral (len a)) a

quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

fastPrint :: (a -> Program t b) -> a -> IO ()
fastPrint prg input = T.putStrLn $ printPrg (prg input)

elen :: (Array a, ASize s) => a s e -> Exp Word32
elen = fromIntegral.len



