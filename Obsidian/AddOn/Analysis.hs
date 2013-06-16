{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis (insertAnalysis) where

import qualified Obsidian.CodeGen.CUDA as CUDA
import Obsidian.CodeGen.Program
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian
import Obsidian.Globs
import Obsidian.AddOn.ExpAnalysis
import Data.Tuple (swap)

import Data.Word
import Data.Int
import Data.Maybe
import Control.Monad

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
insertAnalysis im = im' ++ out (SComment "test")
  where accesses = collectExp getIndicesExp im
                ++ collectIM  getIndicesIM  im
        sizes = getSizes im
        im' = traverseComment (listToMaybe.map show.map inRange.getIndicesIM) im
        inRange (n,e) = ranges
          where ranges = map (getRange M.empty) $ M.keys nes
                nes = linerize e

getRange :: (Num a, Ord a, Scalar a) => M.Map (Exp a) (a,a) -> Exp a -> Maybe (a,a)
getRange = gr
  where
    gr :: (Num a, Ord a, Scalar a) => M.Map (Exp a) (a,a) -> Exp a -> Maybe (a,a)
    gr r (BinOp Add a b) = bop r a b $ \al ah bl bh -> return (al+bl,ah+bh)
    gr r (BinOp Sub a b) = bop r a b $ \al ah bl bh -> return (al-bh,ah-bl)
    gr r (BinOp Mul a b) = bop r a b $ \al ah bl bh -> return (al*bl,ah*bh)
    gr r (BinOp Div a b) = bop r a b $ \al ah bl bh -> guard (bl==bh) >> return (al`div`bh,ah`div`bl)
    gr r (BinOp Mod a b) = bop r a b $ \al ah bl bh -> guard (bl==bh) >> return (max al 0,min ah (bh-1))
    gr r (BinOp BitwiseXor a b) = bop r a b $ \al ah bl bh -> do
      guard (al >= 0 && bl >= 0)
      return (0,(getNext2Powerm ah `max` getNext2Powerm bh))
    gr r (Literal a) = Just (a,a)
    gr r a = M.lookup a r

    bop :: (Num a, Ord a, Scalar a) => M.Map (Exp a) (a,a) -> Exp a -> Exp a -> (a->a->a->a->Maybe (a,a)) -> Maybe (a,a)
    bop r a b f = do
      (al,ah) <- gr r a
      (bl,bh) <- gr r b
      f al ah bl bh

traverseComment f = traverseIM (\a -> map (\s -> (SComment s,())) (maybeToList (f a)) ++ [a])

getSizes :: IM -> M.Map Name Word32
getSizes = M.fromList . collectIM getSizesIM

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
linerize' a@(ThreadIdx X) = [(1, ThreadIdx X)]
linerize' a@(BlockIdx X)  = [(1, BlockIdx X)]
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

