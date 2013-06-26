{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Helpers where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian

import Data.Word
import Data.Tuple
import Data.Int
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as M
import Debug.Trace

strace a = trace (show a) a

quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 


linerize :: (Num a, Ord (Exp a)) => Exp a -> M.Map (Exp a) a
linerize = normalize . linerize'

linerize' :: (Num a) => Exp a -> [(a,Exp a)]
linerize' (BinOp Add a b) = linerize' a ++ linerize' b
linerize' (BinOp Sub a b) = linerize' a ++ (map (\(n,v) -> (-n,v)) $ linerize' b)
linerize' (BinOp Mul (Literal a) b) = map (\(n,v) -> (n*a,v)) $ linerize' b
linerize' (BinOp Mul a (Literal b)) = map (\(n,v) -> (n*b,v)) $ linerize' a
linerize' (Literal a)     = [(a, Literal 1)]
linerize' a@(ThreadIdx X) = [(1, ThreadIdx X)]
linerize' a@(BlockIdx X)  = [(1, BlockIdx X)]
linerize' a               = [(1,a)]

normalize :: (Num a, Ord (Exp a)) => [(a,Exp a)] -> M.Map (Exp a) a
normalize = M.fromListWith (+) . map swap

unLinerize :: (Scalar a, Integral a, Num a, Ord (Exp a)) => M.Map (Exp a) a -> Exp a
unLinerize x = sum [val * fromIntegral p | (val,p) <- M.assocs x]

isWarpConstant (Literal a) = True
isWarpConstant (ThreadIdx X) = False
isWarpConstant (BlockIdx X) = True

collectIndices a = map (\(_,[r]) -> r) $ collectIndex a
  where collectIndex (Index r) = [r]
        collectIndex _ = []

