{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Range (inRange, getRange, getRangeM) where

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

inRange :: (Num a, Ord a, Scalar a, Integral a)
        => M.Map String a
        -> (String, Exp a, Bool, IMDataA a)
        -> Maybe String
inRange sizes (n,e,rw,cs) =
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
                    Just r -> Right $ mapPair (*v) r
        size = M.lookup n sizes 
        range = mapPair sum $ unzip ranges
        outofrange = not (range `rangeInSize` fromJust size)

getRange :: (Num a, Ord a, Scalar a, Integral a)
         => IMDataA a -> Exp a -> Maybe (Integer,Integer)
getRange d = maybePair . getRangeM d

getRangeM :: (Num a, Ord a, Scalar a, Integral a)
          => IMDataA a -> Exp a -> (Maybe Integer,Maybe Integer)
getRangeM = gr'
  where
    gr' :: (Num a, Ord a, Scalar a, Integral a)
        => IMDataA a -> Exp a -> (Maybe Integer,Maybe Integer)
    gr' r a = mapPair2 mplus (lookupRangeM r a) (gr r a)

    gr :: (Num a, Ord a, Scalar a, Integral a) => IMDataA a -> Exp a -> (Maybe Integer,Maybe Integer)
    gr r (BinOp Add a b) = bop r a b $ \al ah bl bh -> (maybe2 (+) al bl,maybe2 (+) ah bh)
    gr r (BinOp Sub a b) = bop r a b $ \al ah bl bh -> (maybe2 (-) al bh,maybe2 (-) ah bl)
    gr r (BinOp Mul a b) = bop r a b $ \al ah bl bh -> (maybe2 (*) al bl,maybe2 (*) ah bh)
    gr r (BinOp Div a b) = bop r a b $ \al ah bl bh -> mapPair (guard (bl==bh) >>)
      (maybe2 div al bh, maybe2 div ah bl)
    gr r (BinOp Mod a b) = bop r a b $ \al ah bl bh -> mapPair (guard (bl==bh) >>)
      (fmap (max 0) al,maybe2 min ah (fmap (+ (-1)) bh))
    gr r (BinOp BitwiseXor a b) = bop r a b $ \al ah bl bh -> mapPair (guard (al >= Just 0 && bl >= Just 0) >>)
      (Just 0,maybe2 max (fmap getNext2Powerm ah) (fmap getNext2Powerm bh))
    gr r (Literal a) = (Just $ fromIntegral a,Just $ fromIntegral a)
    gr r a = (Nothing,Nothing)

    bop :: (Num a, Ord a, Scalar a, Integral a)
        => IMDataA a -> Exp a -> Exp a
        -> (Maybe Integer -> Maybe Integer -> Maybe Integer -> Maybe Integer
          -> (Maybe Integer,Maybe Integer))
        -> (Maybe Integer,Maybe Integer)
    bop r a b f = f al ah bl bh
      where (al,ah) = gr' r a
            (bl,bh) = gr' r b

