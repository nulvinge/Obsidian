{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Cost (insertCost, diverges, sumCost, sumCostT, addIMCostT) where

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
import qualified Data.VMultiSet as MS
import Debug.Trace

insertCost :: (Statement a, IMData) -> IMData
insertCost (p,d) = addIMCostT d costt
  where
    costt = case p of
              SCond          e _ -> getECost e --better this
              SSeqFor n      e _ -> getECost e
              SSeqWhile      e _ -> getECost e `mulCostT` 2 --guess
              SForAll        e _ -> getECost e
              SForAllBlocks  e _ -> getECost e
              SForAllThreads e _ -> getECost e
              SAssign _      l e -> (sumCostT $ (collectExp calcECost e)
                                             ++ (collectExp calcECost l))
              SAtomicOp _ _  e _ -> sumCostT (collectExp calcECost e)
              SSynchronize       -> syncCostT
              _                  -> noCostT

    getECost :: (Scalar a) => Exp a -> CostT
    getECost = sumCostT . collectExp calcECost
    calcECost :: Exp a -> [CostT]
    calcECost (Index (n,[r])) = []
    calcECost (BinOp op a b)  = [opCostT]
    calcECost (UnOp op a)     = [opCostT]
    calcECost _               = [noCostT]

mkCost t c = (c,c`mulCostT`t)

mulCostT ms a = MS.mul a ms
addCostT = MS.union

addCost = mapPair2 addCostT

mulCost c t = mapPair ((flip mulCostT) t) c

sumCost = foldr (mapPair2 addCostT) noCost
sumCostT = foldr addCostT noCostT

seqCost :: Cost -> CostT -> Word32 -> Cost
seqCost (d,w) c t = (d `addCostT` c
                    ,w `addCostT` (c `mulCostT` t))


makeCost :: IMData -> CostT -> Cost
makeCost d c = mkCost pars (c `mulCostT` seqs)
  where seqs = product $ map range (getSeqLoops d)
        pars = product $ map range (nub $ (ThreadIdx X) : getParLoops d)
        range :: Exp Word32 -> Integer
        range (BlockIdx X) = 1
        range (ThreadIdx X) = warpsize * fromIntegral (((th+1) `cdiv` warpsize) - (tl `div` warpsize))
          where Just (tl,th) = getRange d (ThreadIdx X)
        range e = ((1+) . (uncurry $ flip (-)) . fromMaybe (0,8) . getRange d) e

addIMCost d c = setCost d (getCost d `addCost` c)
addIMCostT d c = addIMCost d (makeCost d c)

diverges :: (Statement IMData, IMData) -> [Maybe String]
diverges (SCond e ((_,d2):_), d1) =
  if sameRange && containsThreadIdx e
    then [Just "This condition causes divergence issues"]
    else [Nothing]
  where
    warprange d = mapPair (*warpsize) (tl `div` warpsize, (th+1)`cdiv`warpsize)
      where Just (tl,th) = getRange d (ThreadIdx X)
    sameRange = mapPair2 (==) (warprange d1) (warprange d2) == (True,True)

    containsThreadIdx :: (Scalar a) => Exp a -> Bool
    containsThreadIdx e = or (collectExp isThreadIdx e)
    isThreadIdx :: Exp a -> [Bool]
    isThreadIdx (ThreadIdx X) = [True]
    isThreadIdx _             = [False]
diverges _ = []

