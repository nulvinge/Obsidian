{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Cost (insertCost) where

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

insertCost :: IMList IMData -> (IMList IMData,Cost)
insertCost im = (im',sumCost costs)
  where (im',costs) = traverseIMaccUp g im
        g :: [Cost] -> (Statement IMData, IMData)
          -> ((Statement IMData,IMData), Cost)
        g cl (p,d) = ((p,setCost d cost),trace (show threads ++ show (tl,th,warpsize)) cost)
          where cb = sumCost cl
                getUpperD = fromIntegral . fromMaybe 8 . getUpper d
                Just (tl, th) = getRange d (ThreadIdx X)
                threads :: Word32
                threads = warpsize * fromIntegral (((th+1) `cdiv` warpsize) - (tl `div` warpsize))
                cost = case p of
                        SCond          e _ -> seqCost cb (getECost e) threads --better this
                        SSeqFor _      e _ -> seqCost (cb `mulCost` getUpperD e) (getECost e) threads
                        SSeqWhile      e _ -> seqCost cb (getECost e) 1 `mulCost` 2 --guess
                        SForAll        e _ -> seqCost cb (getECost e) threads
                        SForAllBlocks  e _ -> seqCost cb (getECost e) threads
                        SForAllThreads e _ -> seqCost cb (getECost e) threads
                        SAssign _      l e -> mkCost threads (writeCostT
                                           `addCostT` (sumCostT $ (collectExp calcECost e)
                                                               ++ (collectExp calcECost l)))
                        SAtomicOp _ _  e _ -> mkCost threads (writeCostT
                                           `addCostT` (sumCostT (collectExp calcECost e)))
                        SSynchronize       -> mkCost threads syncCostT
                        _                  -> noCost

        getECost :: (Scalar a) => Exp a -> CostT
        getECost = sumCostT . collectExp calcECost
        calcECost :: Exp a -> [CostT]
        calcECost (Index (n,[r])) = [readCostT]
        calcECost (BinOp op a b)  = [opCostT]
        calcECost (UnOp op a)     = [opCostT]
        calcECost _               = [noCostT]


