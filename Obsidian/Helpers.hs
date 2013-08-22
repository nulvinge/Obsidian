{-# LANGUAGE GADTs,
             ScopedTypeVariables,
             FlexibleContexts
             #-}

module Obsidian.Helpers where

import Obsidian.Globs
import Obsidian.Exp

import qualified Data.Map as M
import Data.List
import Data.Maybe
import Data.Either
import Data.Bits
import Control.Monad


linerizel :: (Num a, Ord (Exp a), Eq a, Integral a) => Exp a -> [(Exp a,Integer)]
linerizel = M.toList . linerize

linerize :: (Num a, Ord (Exp a), Eq a, Integral a) => Exp a -> M.Map (Exp a) Integer
linerize = M.filter (/=0) . M.fromListWith (+) . linerize'

linerize' :: (Num a, Integral a) => Exp a -> [(Exp a,Integer)]
linerize' (BinOp Add a b) = linerize' a ++ linerize' b
linerize' (BinOp Sub a b) = linerize' a ++ (map (\(v,n) -> (v,-n)) $ linerize' b)
linerize' (BinOp Mul (Literal a) b) = map (\(v,n) -> (v,n*fromIntegral a)) $ linerize' b
linerize' (BinOp Mul a (Literal b)) = map (\(v,n) -> (v,n*fromIntegral b)) $ linerize' a
linerize' (BinOp Div a (Literal b)) = if ins == []
        then const
        else ((unLinerizel ins)`div`fromIntegral b,1) : const
  where (outs,ins) = partition ((==0).(`mod`fromIntegral b).snd) $ linerizel a
        const = map (mapSnd (`div`fromIntegral b)) outs
linerize' (BinOp Mod a (Literal b)) = [((unLinerizel ins)`mod`fromIntegral b,1)]
  where ins = filter ((/=0).(`mod`fromIntegral b).snd) $ linerizel a
linerize' (BinOp op a b) | isJust $ isDistributive op a b = [(BinOp op ea eb,mm)]
  where mm = foldr1 gcd $ map snd la ++ map snd lb
        (la,lb,ea,eb) = fromJust $ isDistributive op a b
        g :: (Scalar a, Integral a) => Exp a -> Exp a
        g = unLinerizel . map (\(v,n) -> (v,n`div`mm)) . linerizel
        isDistributive :: (Integral c, Scalar c) => Op ((a,b) -> c) -> Exp a -> Exp b
                       -> Maybe ([(Exp a,Integer)], [(Exp b,Integer)], Exp a, Exp b)
        isDistributive Max a b = Just (linerizel a,linerizel b,g a,g b)
        isDistributive Min a b = Just (linerizel a,linerizel b,g a,g b)
        isDistributive _   _ _ = Nothing
linerize' (Literal a)     = [(Literal 1, fromIntegral a)]
linerize' a@(ThreadIdx X) = [(ThreadIdx X,1)]
linerize' a@(BlockIdx X)  = [(BlockIdx X, 1)]
linerize' a               = [(a,          1)]

unLinerizel :: (Scalar a, Integral a, Num a, Ord (Exp a)) => [(Exp a,Integer)] -> Exp a
unLinerizel x = sum [val * fromIntegral p | (val,p) <- x, p /= 0]

unLinerize :: (Scalar a, Integral a, Num a, Ord (Exp a)) => M.Map (Exp a) Integer -> Exp a
unLinerize = unLinerizel . M.assocs

maxDivable :: (Num a, Ord (Exp a), Eq a, Integral a) => Exp a -> Integer
maxDivable = foldr1 gcd . map snd . linerizel 

warpsize :: (Num a) => a
warpsize = 32

--usefull functions

mapPair f (a,b) = (f a, f b)
mapPair2 f (a1,b1) (a2,b2) = (a1 `f` a2, b1 `f` b2)

mapFst f (a,b) = (f a, b)
mapSnd f (a,b) = (a, f b)

maybePair (Just a, Just b) = Just (a,b)
maybePair _                = Nothing

maybe2 f (Just a) (Just b) = Just $ f a b
maybe2 f _        _        = Nothing

boolToMaybe p a = if p then Just a else Nothing

a `cdiv` b = (a+b-1)`div`b

list a = [a]

comp2 a b c d = a (b c d)

partitionMaybes :: (a -> Maybe b) -> [a] -> ([b],[a])
partitionMaybes p = partitionEithers . map g
  where g a = case p a of
                Nothing -> Right a
                Just b  -> Left  b

isLeft (Left _)  = True
isLeft (Right _) = False
isRight = not . isLeft

