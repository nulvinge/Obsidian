{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Range (inRange, makeRanges) where

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
import Control.Monad
import qualified Data.Map as M

makeRanges :: Conds -> M.Map (Exp Word32) (Word32, Word32)
makeRanges = M.mapMaybe maybeRange . M.fromListWith minmax . concat . strace . map makeRange
  where
    makeRange :: Exp Bool -> [(Exp Word32, (Maybe Word32, Maybe Word32))]
    makeRange (BinOp o a b) = makeRangeB (witness a) o a b
    makeRange _ = []
    makeRangeB :: Witness a -> (Op ((a,b) -> Bool)) -> Exp a -> Exp b
               -> [(Exp Word32, (Maybe Word32, Maybe Word32))]
    makeRangeB Word32Witness Eq  a b = makeInEq (a-b)  $ \v -> (Just v, Just v)
    makeRangeB Word32Witness Lt  a b = makeInEq (a-b+1)$ \v -> (Nothing,Just v)
    makeRangeB Word32Witness LEq a b = makeInEq (a-b)  $ \v -> (Nothing,Just v)
    makeRangeB Word32Witness Gt  a b = makeInEq (a-b-1)$ \v -> (Just v,Nothing)
    makeRangeB Word32Witness GEq a b = makeInEq (a-b)  $ \v -> (Just v,Nothing)
    makeRangeB BoolWitness And a b = makeRange a ++ makeRange b
    makeRangeB _ _ _ _ = []

    minmax (a1,b1) (a2,b2) = (mergeMaybies max a1 a2, mergeMaybies min b1 b2)
    mergeMaybies f a b = case catMaybes [a,b] of
                          []    -> Nothing
                          [a]   -> Just a
                          [a,b] -> Just $ f a b
    maybeRange (Just a, Just b) = Just (a,b)
    maybeRange _                = Nothing

    makeInEq :: Exp Word32
             -> (Exp Word32 -> (Maybe (Exp Word32), Maybe (Exp Word32)))
             -> [(Exp Word32, (Maybe Word32,Maybe Word32))]
    makeInEq a f = map solToRange $ solveIneq a
      where solToRange (var,val,left) =
              if left
                then (var,mapPair expToMaybe $        f val)
                else (var,mapPair expToMaybe $ swap $ f val)
            mapPair f (a,b) = (f a, f b)
            expToMaybe (Just (Literal a)) = Just a
            expToMaybe _                  = Nothing

    solveIneq :: Exp Word32 -> [(Exp Word32, Exp Word32, Bool)]
    solveIneq x = [(e, move p $ M.delete e m, p >= 0)
                  | (e,p) <- M.assocs m , p/=0 , e/=1]
      where m = linerize x
            move p a = (-(unLinerize a)) `div` fromIntegral (abs p)


inRange sizes (n,e,cs) =
  if isNothing size
    then Just $ "no size info about " ++ n
    else if any isNothing ranges
      then if outofrange
        then Just "probbably out of range"
        else Just $ "indeterminate because " ++ (show $ catMaybes indets)
                ++ " has no range"
      else if outofrange
        then Just $ "definatly out of range: " ++ (show range)
                ++ " does not fit in " ++ n ++ " with size " ++ (show size)
        else Nothing
  where ranges = map (\(e,v) -> getRange cs e >>= pairMul v) $ M.assocs (linerize e)
        pairMul a (l,h) = Just (l*a,h*a)
        size = M.lookup n sizes 
        range = let (l,h) = unzip $ catMaybes ranges
                in (sum l,sum h)
        outofrange = (fst range < 0) || (fromJust size <= snd range)
        indets = map (\(e,v) -> if isNothing (getRange cs e) then Just (e,cs) else Nothing) $ M.assocs (linerize e)

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

    bop :: (Num a, Ord a, Scalar a)
        => M.Map (Exp a) (a,a) -> Exp a -> Exp a
        -> (a -> a-> a -> a -> Maybe (a,a)) -> Maybe (a,a)
    bop r a b f = do
      (al,ah) <- gr r a
      (bl,bh) <- gr r b
      f al ah bl bh

