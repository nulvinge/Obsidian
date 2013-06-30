{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Cost (insertCost, sumCost, makeCost) where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian.AddOn.Analysis.Range
import Obsidian.AddOn.Analysis.Helpers

import Data.Word
import Data.Tuple
import Data.Int
import Data.Maybe
import Data.Either
import Data.List
import Control.Monad
import qualified Data.Map as M
import Debug.Trace

insertCost :: (Statement a, IMData) -> IMData
insertCost (p,d) = setCost d cost
  where
    cost = makeCost d costt
    costt = case p of
              SCond          e _ -> getECost e --better this
              SSeqFor n      e _ -> getECost e
              SSeqWhile      e _ -> getECost e `mulCostT` 2 --guess
              SForAll        e _ -> getECost e
              SForAllBlocks  e _ -> getECost e
              SForAllThreads e _ -> getECost e
              SAssign _      l e -> writeCostT `addCostT`
                                        (sumCostT $ (collectExp calcECost e)
                                      ++ (collectExp calcECost l))
              SAtomicOp _ _  e _ -> writeCostT `addCostT` sumCostT (collectExp calcECost e)
              SSynchronize       -> syncCostT
              _                  -> noCostT

    getECost :: (Scalar a) => Exp a -> CostT
    getECost = sumCostT . collectExp calcECost
    calcECost :: Exp a -> [CostT]
    calcECost (Index (n,[r])) = [readCostT]
    calcECost (BinOp op a b)  = [opCostT]
    calcECost (UnOp op a)     = [opCostT]
    calcECost _               = [noCostT]

opCostT    = CostT 1 0 0 0
readCostT  = CostT 0 1 0 0
writeCostT = CostT 0 0 1 0
syncCostT  = CostT 0 0 0 1

mkCost t c = (c,c`mulCostT`t)

addCostT :: CostT -> CostT -> CostT
addCostT (CostT o1 r1 w1 s1) (CostT o2 r2 w2 s2) = CostT (o1+o2) (r1+r2) (w1+w2) (s1+s2)

mulCostT (CostT o r w s) t = CostT (o*t) (r*t) (w*t) (s*t)

mulCost c t = mapPair ((flip mulCostT) t) c

sumCost = foldr (mapPair2 addCostT) noCost
sumCostT = foldr addCostT noCostT

seqCost :: Cost -> CostT -> Word32 -> Cost
seqCost (d,w) c t = (d `addCostT` c
                    ,w `addCostT` (c `mulCostT` t))


makeCost d c = mkCost pars (c `mulCostT` seqs)
  where seqs = product $ map range (getSeqLoopFactor d)
        pars = product $ map range (getParLoopFactor d)
        range :: Exp Word32 -> Word32
        range (BlockIdx X) = 1
        range (ThreadIdx X) = warpsize * fromIntegral (((th+1) `cdiv` warpsize) - (tl `div` warpsize))
          where Just (tl,th) = getRange d (ThreadIdx X)
        range e = ((1+) . (uncurry $ flip (-)) . fromMaybe (0,8) . getRange d) e

