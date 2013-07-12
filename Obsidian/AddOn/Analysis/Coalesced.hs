{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Coalesced (isCoalesced) where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian.AddOn.Analysis.Helpers
import Obsidian.AddOn.Analysis.Range

import Data.Word
import Data.Tuple
import Data.Int
import Data.List
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as M


isCoalesced :: (Num Word32, Ord Word32, Scalar Word32, Integral Word32)
            => (String, Exp Word32, Bool, IMData)
            -> (CostT,Maybe String)
isCoalesced (n,e,rw,cs) = appendCost (isLocal n) rw $
  if nonConstants /= []
    then Just $ "The following variables are not warp constant: " ++ (show nonConstants)
    else if stride == 0 --broadcast
         || stride == 1 --coalesced
      then if nonConstantsAll /= []
        then Just $ "The following variables are not warp constant: " ++ (show nonConstantsAll)
        else Nothing
      else if (32 `mod` stride /= 0 --different banks
           && stride `mod` 32 /= 0) --unnecesary since `mod`32 is already done.
        then Nothing
        else Just $ "Bank conflicts with a factor of: " ++ (show stride)
                  -- ++ " gives a slowdown of about " ++ (show $ stride)
  where e' = simplifyMod' 32 e
        m = linerize e
        stride = fromMaybe 0 $ M.lookup (ThreadIdx X) m
        nonConstants = filter (not.isWarpConstant) $ M.keys $ linerize e'
        nonConstantsAll = filter (not.isWarpConstant) $ M.keys $ linerize e

        isWarpConstant :: Scalar a => Exp a -> Bool
        isWarpConstant (ThreadIdx X) = True --handled above with stride
        isWarpConstant e = and $ collectExp f e
          where f :: Scalar a => Exp a -> [Bool]
                f = (map (\a -> isWarpConstant' (witness a) a) . getLeaves)

        isWarpConstant' :: Witness a -> Exp a -> Bool
        isWarpConstant' _ (Literal a)   = True
        isWarpConstant' _ (BlockIdx X)  = True
        isWarpConstant' Word32Witness a = getBlockConstant cs a
        --isWarpConstant _ = False --further analysis required, but should be good for the most obious cases
        appendCost :: Bool -> Bool -> Maybe String -> (CostT, Maybe String)
        appendCost gl rw s = (accessCostT gl rw (isJust s), s)

 
simplifyMod :: (Num a, Bounded a, Ord a, Scalar a, Integral a)
            => IMDataA a
            -> a -> Exp a -> Exp a
simplifyMod cs m = maybeMod cs m . simplifyMod' m

maybeMod cs m v = fromMaybe (v `mod` fromIntegral m) e
  where e = do
          r <- getRange cs v
          guard $ r `rangeInSize` m
          return v

simplifyMod' :: (Num a, Ord a, Scalar a, Integral a)
            => a -> Exp a -> Exp a
simplifyMod' m = unLinerizel . map simplify . linerizel
  where simplify (e,v) = (e,v`mod` fromIntegral m) --further simplifications may be possible, as below
        --sm :: Exp Word32 -> (Exp Word32)
        --sm (BinOp Div a b) = sm a `div` b
        --sm (BinOp Mod a bb@(Literal b)) = simplifyMod cs b


