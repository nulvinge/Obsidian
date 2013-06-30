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
import qualified Data.Set as S
import Debug.Trace

type Cost = Int

type IMData = IMDataA Word32
data IMDataA a = IMDataA
  { getUpperMap :: M.Map (Exp a) a
  , getLowerMap :: M.Map (Exp a) a
  , getBlockConstantSet :: S.Set (Exp a)
  , getCost :: Cost
  }

getUpper :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Maybe a
getUpper d e = M.lookup e (getUpperMap d)

getLower :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Maybe a
getLower d e = M.lookup e (getLowerMap d)

lookupRangeM :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> (Maybe a,Maybe a)
lookupRangeM d e = (getLower d e, getUpper d e)

lookupRange :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Maybe (a,a)
lookupRange d = maybePair . lookupRangeM d

getBlockConstant :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Bool
getBlockConstant d e = S.member e (getBlockConstantSet d)

setCost (IMDataA l u b _) c = (IMDataA l u b c)

strace a = trace (show a) a

quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 

linerizel :: (Num a, Ord (Exp a), Eq a) => Exp a -> [(Exp a,a)]
linerizel = M.toList . linerize

linerize :: (Num a, Ord (Exp a), Eq a) => Exp a -> M.Map (Exp a) a
linerize = M.filter (/=0) . M.fromListWith (+) . linerize'

linerize' :: (Num a) => Exp a -> [(Exp a,a)]
linerize' (BinOp Add a b) = linerize' a ++ linerize' b
linerize' (BinOp Sub a b) = linerize' a ++ (map (\(v,n) -> (v,-n)) $ linerize' b)
linerize' (BinOp Mul (Literal a) b) = map (\(v,n) -> (v,n*a)) $ linerize' b
linerize' (BinOp Mul a (Literal b)) = map (\(v,n) -> (v,n*b)) $ linerize' a
linerize' (Literal a)     = [(Literal 1,  a)]
linerize' a@(ThreadIdx X) = [(ThreadIdx X,1)]
linerize' a@(BlockIdx X)  = [(BlockIdx X, 1)]
linerize' a               = [(a,          1)]

unLinerizel :: (Scalar a, Integral a, Num a, Ord (Exp a)) => [(Exp a,a)] -> Exp a
unLinerizel x = sum [val * fromIntegral p | (val,p) <- x, p /= 0]

unLinerize :: (Scalar a, Integral a, Num a, Ord (Exp a)) => M.Map (Exp a) a -> Exp a
unLinerize = unLinerizel . M.assocs

collectIndices a = map (\(_,[r]) -> r) $ collectIndex a
  where collectIndex (Index r) = [r]
        collectIndex _ = []

rangeIn (ls,hs) (lb,hb) = ls >= lb && hs <= hb
rangeInSize r s = r `rangeIn` (0,s-1)

mapPair f (a,b) = (f a, f b)
mapPair2 f (a1,b1) (a2,b2) = (a1 `f` a2, b1 `f` b2)

maybePair (Just a, Just b) = Just (a,b)
maybePair _                = Nothing

maybe2 f (Just a) (Just b) = Just $ f a b
maybe2 f _        _        = Nothing

boolToMaybe p a = if p then Just a else Nothing

a `cdiv` b = (a+b-1)`div`b

