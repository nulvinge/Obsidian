{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             NoMonomorphismRestriction,
             FlexibleInstances #-}

module Obsidian.Dependency.Helpers
  ( module Obsidian.Dependency.Helpers
  , module Data.Word
  , module Data.Tuple
  , module Data.Int
  , module Data.List
  , module Data.Maybe
  , module Data.Either
  , module Data.Bits
  , module Control.Monad
  , module Obsidian.Globs
  , module Obsidian.Exp
  , module Obsidian.Array
  , module Obsidian.Types
  , module Obsidian.Library
  , module Obsidian.Program
  , module Obsidian.Helpers
  , module Obsidian.CodeGen.Program
  , module Obsidian.Dependency.ExpAnalysis
  , module Debug.Trace
  ) where

--import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian.Globs
import Obsidian.Dependency.ExpAnalysis
import Obsidian.Helpers
import Obsidian.Exp
import Obsidian.Array
import Obsidian.Types
import Obsidian.Library hiding (zip)
import Obsidian.Program

import Data.Word
import Data.Tuple
import Data.Tuple.Enum
import Data.Int
import Data.List hiding (drop,last,replicate,reverse,splitAt,take,zipWith)
import Data.Maybe
import Data.Either
import Data.Bits
import Control.Monad
import Debug.Trace

import qualified Data.List as L
import qualified Data.VMultiSet as MS
import qualified Data.Map as M
import qualified Data.Set as S

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

collectIndices a = map (\(_,[r]) -> r) $ collectIndex a
  where collectIndex (Index r) = [r]
        collectIndex _ = []

type Access = (Name, Exp Word32, Bool, IMData, (Int,Int))
getAccessesIM :: (Statement IMData, IMData) -> [Access]
getAccessesIM = map g
              . L.reverse --makes reads come before writes
              . zip [0..]
              . getIndicesIM
  where g (i,(n,e,l,d)) = (n,e,l,d,(getInstruction d,i))



rangeIn (ls,hs) (lb,hb) = ls >= fromIntegral lb && hs <= fromIntegral hb
rangeIntersect (ls,hs) (lb,hb) = not $ hs < lb || hb < ls
rangeInSize r s = r `rangeIn` (0,s-1)

isLocal n | "arr"    `isPrefixOf` n = True
          | "input"  `isPrefixOf` n = False
          | "output" `isPrefixOf` n = False
          | otherwise = error n

