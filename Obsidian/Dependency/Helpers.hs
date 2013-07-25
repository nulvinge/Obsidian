{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             NoMonomorphismRestriction,
             FlexibleInstances #-}

module Obsidian.Dependency.Helpers where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian.Globs
import Obsidian.Dependency.ExpAnalysis
import Obsidian

import Data.Word
import Data.Tuple
import Data.Tuple.Enum
import Data.Int
import Data.List
import Data.Maybe
import Data.Either
import Data.Bits
import Control.Monad
import qualified Data.VMultiSet as MS
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

type Cost = (CostT,CostT)

data CostLocation = GlobalMem | SharedMem | LocalMem | ConstantMem | ImageMem
  deriving (Show, Eq, Enum, Bounded)
data CostAccessType = Coalesced | Parallel | Broadcast | BankConflict | Sequential
  deriving (Show, Eq, Enum, Bounded)
data CostType = Writes CostLocation CostAccessType
              | Reads  CostLocation CostAccessType
              | Operations
              | Syncs
  deriving (Show)
instance Enum CostType where
  fromEnum (Operations) = 0
  fromEnum (Syncs) = 1
  fromEnum (Writes a b) = 2+fromEnum (False,a,b)
  fromEnum (Reads  a b) = 2+fromEnum (True,a,b) 
  toEnum 0 = Operations
  toEnum 1 = Syncs
  toEnum i = let (rw,a,b) = toEnum (i-2)
             in (if rw then Reads else Writes) a b

--maxAcces = fromEnum (maxBound :: (CostLocation,CostAccessType))


instance Bounded CostType where
  minBound = Operations
  maxBound = let (rw,a,b) = (maxBound :: (Bool,CostLocation,CostAccessType))
             in (if rw then Reads else Writes) a b


type CostT = MS.MultiSet CostType

showCost :: Cost -> [String]
showCost = map (\((i,s),(i',p)) -> show s ++ "\t/ " ++ show p ++ "\t" ++ show i)
         . uncurry zip
         . mapPair MS.toOccurList

noCostT = MS.empty
accessCostT :: Bool -> CostLocation -> CostAccessType -> CostT
accessCostT rw gl ps = MS.singleton $ (if rw then Reads else Writes) gl ps
opCostT  = MS.singleton Operations
syncCostT= MS.singleton Syncs
noCost = (noCostT, noCostT)

type IMData = IMDataA Word32
data IMDataA a = IMDataA
  { getComments :: [String]
  , getUpperMap :: M.Map (Exp a) Integer
  , getLowerMap :: M.Map (Exp a) Integer
  , getBlockConstantSet :: S.Set (Exp a)
  , getCost :: Cost
  , getLoops :: [(Exp Word32, Bool)]
  -- , getArrayScope :: M.Map Name (Exp Word32)
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

getLoopsBelow n d = dropWhile ((/= getMemoryLevel n d) . fst) $ getLoops d

getMemoryLevel n d  --this is all guesswork
  | "arr"    `isPrefixOf` n = ThreadIdx X
  | "input"  `isPrefixOf` n = BlockIdx X
  | "output" `isPrefixOf` n = BlockIdx X
  | otherwise = error n

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

