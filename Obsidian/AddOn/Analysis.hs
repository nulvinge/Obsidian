{-# LANGUAGE GADTs,
             TypeFamilies,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis (insertAnalysis) where

import qualified Obsidian.CodeGen.CUDA as CUDA
import Obsidian.CodeGen.Program
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian
import Obsidian.AddOn.ExpAnalysis
import Data.Tuple (swap)

import Data.Word
import Data.Int

import qualified Data.Map as M

instance ToProgram (Inputs,IM) where
  toProgram i a () = a

type instance InputList (Inputs,IM)    = () 

-- Coalesced

quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 

printAnalysis :: ToProgram prg => prg -> InputList prg -> IO ()
printAnalysis p a = quickPrint (ins, insertAnalysis im) ()
    where (ins,im) = toProgram 0 p a

insertAnalysis :: IM -> IM
insertAnalysis a = a ++ out (SComment "test")



input1 :: Pull (Exp Word32) EInt 
input1 = namedGlobal "apa" (variable "X")

t0 = printAnalysis (pushGrid 32 . fmap (+1). ixMap (+5)) (input1 :- ())

collectIndices a = map (\(_,[r]) -> r) $ collectIndex a
  where collectIndex (Index r) = [r]
        collectIndex _ = []

linerize :: (Num a, Ord (Exp a)) => Exp a -> M.Map (Exp a) a
linerize = normalize . linerize'

linerize' :: (Num a) => Exp a -> [(a,Exp a)]
linerize' (BinOp Add a b) = linerize' a ++ linerize' b
linerize' (BinOp Mul (Literal a) b) = map (\(n,v) -> (n*a,v)) $ linerize' b
linerize' (BinOp Mul a (Literal b)) = map (\(n,v) -> (n*b,v)) $ linerize' a
linerize' (Literal a)     = [(a, Literal 1)]
linerize' a@(ThreadIdx X) = [(fromIntegral 1, ThreadIdx X)]
linerize' a@(BlockIdx X)  = [(fromIntegral 1, BlockIdx X)]
linerize' a               = [(1,a)]

normalize :: (Num a, Ord (Exp a)) => [(a,Exp a)] -> M.Map (Exp a) a
normalize = M.fromListWith (+) . map swap

isWarpConstant (Literal a) = True
isWarpConstant (ThreadIdx X) = False
isWarpConstant (BlockIdx X) = True



-- Hazards

-- Memory

--analyzeMemory :: GProgram () -> Int
--analyzeMemory p = 
--  let compiledP = compile p -- allocate memory

