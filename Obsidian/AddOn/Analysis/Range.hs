{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Range (inRange, getRange) where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian.AddOn.Analysis.Helpers

import Data.Word
import Data.Tuple
import Data.Int
import Data.Maybe
import Data.Either
import Data.List
import Control.Monad
import qualified Data.Map as M

inRange :: (Num a, Ord a, Scalar a)
        => M.Map [Char] a
        -> ([Char], Exp a, IMDataA a)
        -> Maybe [Char]
inRange sizes (n,e,cs) =
  if isNothing size
    then Just $ "no size info about " ++ n
    else if indets /= []
      then if outofrange
        then Just "probably out of range"
        else Just $ "indeterminate because the ranges of "
                ++ (show indets) ++ " are unknown"
      else if outofrange
        then Just $ "definitely out of range: " ++ (show range)
                ++ " does not fit in " ++ n ++ " with size " ++ (show size)
        else Nothing
  where (indets, ranges) = partitionEithers $ map g $ M.assocs (linerize e)
        g (e,v) = case getRange cs e of
                    Nothing -> Left e
                    Just e' -> Right $ mapPair (*v) e'
        size = M.lookup n sizes 
        range = mapPair sum $ unzip ranges
        outofrange = not (range `rangeInSize` fromJust size)

getRange :: (Num a, Ord a, Scalar a) => IMDataA a -> Exp a -> Maybe (a,a)
getRange = gr'
  where
    gr' :: (Num a, Ord a, Scalar a) => IMDataA a -> Exp a -> Maybe (a,a)
    gr' r a = b `mplus` (gr r a)
      where b = do (l,h,s) <- M.lookup a r
                   return (l,h)

    gr :: (Num a, Ord a, Scalar a) => IMDataA a -> Exp a -> Maybe (a,a)
    gr r (BinOp Add a b) = bop r a b $ \al ah bl bh -> return (al+bl,ah+bh)
    gr r (BinOp Sub a b) = bop r a b $ \al ah bl bh -> return (al-bh,ah-bl)
    gr r (BinOp Mul a b) = bop r a b $ \al ah bl bh -> return (al*bl,ah*bh)
    gr r (BinOp Div a b) = bop r a b $ \al ah bl bh -> guard (bl==bh) >> return (al`div`bh,ah`div`bl)
    gr r (BinOp Mod a b) = bop r a b $ \al ah bl bh -> guard (bl==bh) >> return (max al 0,min ah (bh-1))
    gr r (BinOp BitwiseXor a b) = bop r a b $ \al ah bl bh -> do
      guard (al >= 0 && bl >= 0)
      return (0,(getNext2Powerm ah `max` getNext2Powerm bh))
    gr r (Literal a) = Just (a,a)
    gr r a = Nothing

    bop :: (Num a, Ord a, Scalar a)
        => IMDataA a -> Exp a -> Exp a
        -> (a -> a-> a -> a -> Maybe (a,a)) -> Maybe (a,a)
    bop r a b f = do
      (al,ah) <- gr' r a
      (bl,bh) <- gr' r b
      f al ah bl bh

