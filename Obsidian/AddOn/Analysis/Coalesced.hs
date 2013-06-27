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
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as M


isCoalesced :: (Num Word32, Ord Word32, Scalar Word32, Integral Word32)
            => ([Char], Exp Word32, IMData)
            -> Maybe [Char]
isCoalesced (n,e,cs) =
  if nonConstants /= []
    then Just $ "The following variables are not warp constant: " ++ (show nonConstants)
    else if tfactor /= 0 && tfactor /= 1
      then Just $ "Bank conflicts with a factor of: " ++ (show tfactor)
      else Nothing
  where e' = simplifyMod' 32 e
        m = linerize e'
        tfactor = fromMaybe 0 $ M.lookup (ThreadIdx X) m
        nonConstants = filter (not.isWarpConstant) $ M.keys m
        isWarpConstant (Literal a)   = True
        isWarpConstant (ThreadIdx X) = True --handled above with tfactor
        isWarpConstant (BlockIdx X)  = True
        isWarpConstant a = c
          where (_,_,c) = M.findWithDefault (undefined, undefined, False) a cs
        --isWarpConstant _ = False --further analysis required, but should be good for the most obious cases

 
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
simplifyMod' m v = unLinerizel [(simplify e v,v`mod`m)  | (e,v) <- linerizel v]
  where simplify e v = e --further simplifications may be possible, as below
        --sm :: Exp Word32 -> (Exp Word32)
        --sm (BinOp Div a b) = sm a `div` b
        --sm (BinOp Mod a bb@(Literal b)) = simplifyMod cs b

