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

insertCost :: IMList IMData -> (IMList IMData,Cost)
insertCost im = (im',sum costs)
  where (im',costs) = traverseIMaccUp g im
        g :: [Cost] -> (Statement IMData, IMData)
          -> ((Statement IMData,IMData), Cost)
        g cl (p,d) = ((p,setCost d cost),cost)
          where cb = sum cl
                getUpper = fromIntegral . snd . fromMaybe (undefined,8) . getRange d
                cost = case p of
                        SCond          e _ -> getECost e + sum cl
                        SSeqFor _      e _ -> getECost e + cb * getUpper e
                        SSeqWhile      e _ ->(getECost e + cb) * 2
                        SForAll        e _ -> getECost e + cb * getUpper e
                        SForAllBlocks  e _ -> getECost e + cb * getUpper e
                        SForAllThreads e _ -> getECost e + cb * getUpper e
                        SAssign _      l e -> 1000 + (sum $ (collectExp calcECost e)
                                                         ++ (collectExp calcECost l))
                        SAtomicOp _ _  e _ -> 1000 + (sum $ collectExp calcECost e)
                        SSynchronize       -> 100000
                        _                  -> 0

        getECost :: (Scalar a) => Exp a -> Cost
        getECost = sum . collectExp calcECost
        calcECost :: Exp a -> [Cost]
        calcECost (Index (n,[r])) = [10000]
        calcECost (BinOp op a b)  = [1]
        calcECost (UnOp op a)     = [1]
        calcECost _               = [0]


