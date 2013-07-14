{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Helpers where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian.Globs
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian

import Data.Word
import Data.Tuple
import Data.Int
import Data.List
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V
import Debug.Trace

type Cost = (CostT,CostT)

type CostT = (V.Vector Integer)

showCost :: Cost -> [String]
showCost = map (\(i,(s,p)) -> show s ++ "\t/ " ++ show p ++ "\t" ++ i)
         . filter (\(i,(s,p)) -> any (/=0) [s,p])
         . zip info
         . uncurry zip
         . mapPair V.toList
  where info = [a ++ c ++ " " ++ b
               | c <- [""," sequential"]
               , b <- ["writes","reads"]
               , a <- ["global", "local"]
               ] ++ ["Ops", "Syncs"]

noCostT  = V.replicate 15 0
accessCostT :: Bool -> Bool -> Bool -> CostT
accessCostT gl rw ps = noCostT V.// [(n,1)]
  where n :: Int
        n = 4*fromEnum ps + 2*fromEnum rw + 1*fromEnum gl
opCostT  = noCostT V.// [(8,1)]
syncCostT= noCostT V.// [(9,1)]
noCost = (noCostT, noCostT)

type IMData = IMDataA Word32
data IMDataA a = IMDataA
  { getComments :: [String]
  , getUpperMap :: M.Map (Exp a) Integer
  , getLowerMap :: M.Map (Exp a) Integer
  , getBlockConstantSet :: S.Set (Exp a)
  , getCost :: Cost
  , getLoops :: [(Exp Word32, Bool)]
  , getInstruction :: Int
  }

instance Show (IMDataA a) where
  show _ = "IMData"

addComments    (IMDataA ss l u b c loop i) ss' = (IMDataA (ss++ss') l u b c loop i)
setCost        (IMDataA ss l u b _ loop i) c   = (IMDataA ss l u b c loop i)
setInstruction (IMDataA ss l u b c loop _) i   = (IMDataA ss l u b c loop i)



getUpper :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Maybe Integer
getUpper d e = M.lookup e (getUpperMap d)

getLower :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Maybe Integer
getLower d e = M.lookup e (getLowerMap d)

lookupRangeM :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> (Maybe Integer,Maybe Integer)
lookupRangeM d e = (getLower d e, getUpper d e)

lookupRange :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Maybe (Integer,Integer)
lookupRange d = maybePair . lookupRangeM d

getBlockConstant :: (Ord a, Scalar a) => IMDataA a -> (Exp a) -> Bool
getBlockConstant d e = S.member e (getBlockConstantSet d)

getSeqLoops, getParLoops :: IMData -> [Exp Word32]
getSeqLoops = map fst . filter ((==False).snd) . getLoops
getParLoops = map fst . filter ((==True ).snd) . getLoops

strace a = trace (show a) a

quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 

linerizel :: (Num a, Ord (Exp a), Eq a, Integral a) => Exp a -> [(Exp a,Integer)]
linerizel = M.toList . linerize

linerize :: (Num a, Ord (Exp a), Eq a, Integral a) => Exp a -> M.Map (Exp a) Integer
linerize = M.filter (/=0) . M.fromListWith (+) . linerize'

linerize' :: (Num a, Integral a) => Exp a -> [(Exp a,Integer)]
linerize' (BinOp Add a b) = linerize' a ++ linerize' b
linerize' (BinOp Sub a b) = linerize' a ++ (map (\(v,n) -> (v,-n)) $ linerize' b)
linerize' (BinOp Mul (Literal a) b) = map (\(v,n) -> (v,n*fromIntegral a)) $ linerize' b
linerize' (BinOp Mul a (Literal b)) = map (\(v,n) -> (v,n*fromIntegral b)) $ linerize' a
linerize' (BinOp Div a (Literal b)) = ((unLinerizel ins)`div`fromIntegral b,1)
                                    : map (mapSnd (`div`fromIntegral b)) outs
  where (outs,ins) = partition ((==0).(`mod`fromIntegral b).snd) $ linerizel a
linerize' (BinOp Mod a (Literal b)) = [((unLinerizel ins)`mod`fromIntegral b,1)]
  where ins = filter ((/=0).(`mod`fromIntegral b).snd) $ linerizel a
linerize' (Literal a)     = [(Literal 1, fromIntegral a)]
linerize' a@(ThreadIdx X) = [(ThreadIdx X,1)]
linerize' a@(BlockIdx X)  = [(BlockIdx X, 1)]
linerize' a               = [(a,          1)]

unLinerizel :: (Scalar a, Integral a, Num a, Ord (Exp a)) => [(Exp a,Integer)] -> Exp a
unLinerizel x = sum [val * fromIntegral p | (val,p) <- x, p /= 0]

unLinerize :: (Scalar a, Integral a, Num a, Ord (Exp a)) => M.Map (Exp a) Integer -> Exp a
unLinerize = unLinerizel . M.assocs

collectIndices a = map (\(_,[r]) -> r) $ collectIndex a
  where collectIndex (Index r) = [r]
        collectIndex _ = []

type Access = (Name, Exp Word32, Bool, IMData, (Int,Int))
getAccessesIM :: (Statement IMData, IMData) -> [Access]
getAccessesIM (p,d) = map g
                    $ Data.List.reverse --makes reads come before writes
                    $ zip [0..]
                    $ getIndicesIM (p,d)
  where g (i,(n,e,l,d)) = (n,e,l,d,(getInstruction d,i))



rangeIn (ls,hs) (lb,hb) = ls >= fromIntegral lb && hs <= fromIntegral hb
rangeIntersect (ls,hs) (lb,hb) = not $ hs < lb || hb < ls
rangeInSize r s = r `rangeIn` (0,s-1)


isLocal n | "arr"    `isPrefixOf` n = True
          | "input"  `isPrefixOf` n = False
          | "output" `isPrefixOf` n = False
          | otherwise = error n

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

warpsize :: (Num a) => a
warpsize = 32

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

