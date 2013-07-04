{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Hazards (hazardChecking) where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian.Globs
import Obsidian
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian.AddOn.Analysis.Helpers
import Obsidian.AddOn.Analysis.Range

import Data.Word
import Data.Tuple
import Data.Int
import Data.List as L
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as M
import Debug.Trace

type Access = (Name, Exp Word32, Bool, IMData)

hazardChecking :: IMList IMData -> IMList IMData
hazardChecking = fst . traverseIMaccDataPrePost pre post ([],[])

pre :: ((Statement IMData, IMData), ([Access], [Access]))
    -> (IMData, ([Access], [Access]))
pre ((SSynchronize, d),(loc,glob)) = (d,([],glob))
pre ((p,d),            (loc,glob)) = (addComments d comments, (loc++local,glob++global))
  where (local,global) = partition (isLocal. \(n,_,_,_)->n) $ getIndicesIM (p,d)
        localCombs  = map (\a -> (a,a)) local  ++ listProduct local  loc  ++ combinations local
        globalCombs = map (\a -> (a,a)) global ++ listProduct global glob ++ combinations global
        comments = getHazards local loc True
                ++ getHazards global glob False
        getHazards current before t = catMaybes
          $ map (\a -> hasHazard True t a a) current
         ++ map (uncurry $ hasHazard False t)
                (listProduct current before ++ combinations local)

post ((p, d),(loc,glob)) = (d,(loc,glob))

listProduct :: [a] -> [b] -> [(a,b)]
listProduct la lb = [(a,b) | a <- la, b <- lb]
combinations :: [a] -> [(a,a)]
combinations l = concat $ map (\(i,ll) -> map (i,) ll) $ zip l (prefixes l)
prefixes :: [a] -> [[a]]
prefixes l = map (`L.take` l) $ L.take (length l) [0..]

hasHazard :: Bool -> Bool -> Access -> Access -> Maybe String
hasHazard same local aa@(an,a,arw,ad) ba@(bn,b,brw,bd)
  | an /= bn                     = Nothing --different arrays
  | arw && brw                   = Nothing --read read
  -- | isJust d && fromJust d /= 0 = Nothing --banerjee
  | gcdTest (a-b)                = Nothing
  | banerjee aa ba               = Nothing
  | liftM2 rangeIntersect (getRange ad a) (getRange bd b) == Just False = Nothing
  | same && sameTBGroup          = Nothing
  | otherwise = Just $ loc sameTBGroup
                    ++ show (same,local,arw,a,brw,b,mds) -- getRange ad ae `rangeIntersects` getRange bd be
      where mds = aa `diffs` ba
            (d0,ds) = trace (show (a,b)) $ strace $ fromJust mds
            sameThread = sameGroup (ThreadIdx X)
            sameBlock  = sameGroup (BlockIdx  X)
            sameTBGroup = sameThread && (local || sameBlock)
            sameGroup e = isJust mds && d0 == 0 &&
                        (  (af == bf && af /= 0)
                        || (getRange ad e == Just (0,0)))
              where (_,af,bf) = fromMaybe (undefined,0,0) $ lookup e ds
            loc True                 = "same thread dependence "
            loc _ | aa `sameWarp` ba = "same warp dependence   "
            loc _                    = ""

sameWarp :: Access -> Access -> Bool
sameWarp aa@(na,a,arw,ad) ba@(nb,b,brw,bd)
  | ad `sameWarpRange` bd && rangeSize (warprange ad) <= 32 = True
  | otherwise = False --needs better analysis

rangeSize (l,h) = h-l

warprange d = mapPair (*warpsize) (tl `div` warpsize, (th+1)`cdiv`warpsize)
  where Just (tl,th) = getRange d (ThreadIdx X)
sameWarpRange d1 d2 = mapPair2 (==) (warprange d1) (warprange d2) == (True,True)

banerjee aa@(na,a,arw,ad) ba@(nb,b,brw,bd) = maybe False (0>) h
                                          || maybe False (>0) l
  where
    (al,ah) = getRangeM ad a
    (bl,bh) = getRangeM bd b
    (l,h) = (liftM2 (-) al bh,liftM2 (-) ah bl)

diffs aa@(na,a,arw,ad) ba@(nb,b,brw,bd) = do
  guard $ getLoops ad == getLoops bd
  (a0,afs) <- getFactors ad a
  (b0,bfs) <- getFactors bd b
  return (a0-b0
         , map (\((e,sp,a),(_,_,b)) -> (e,(sp,a,b))) $ zip afs bfs)

  where
    m = M.filter (==0) $ M.unionWith (+) (linerize a) (linerize (-b))
    fromExp (Literal a) = Just a
    fromExp _           = Nothing

    getFactors :: IMData -> Exp Word32 -> Maybe (Integer, [(Exp Word32,Bool,Integer)])
    getFactors d e = do
        guard $ nonLoopConst == []
        return $ (sum (trace ("test" ++ (show (consts,nonconsts,e'))) consts), factors)
      where e' = linerize e
            factors = map (\(f,ps) -> (f,ps,M.findWithDefault 0 f e')) $ getLoops d
            (consts,nonconsts) = strace $ partitionMaybes (\(k,n) -> liftM (n*) $ getConst k)
                               $ M.toList e'
            nonLoopConst       = filter (\(k,_) -> not $ any ((==k).fst) $ getLoops d) nonconsts
            getConst a = do
              (l,h) <- getRange d a
              guard $ l==h
              Just l

gcdTest :: Exp Word32 -> Bool
gcdTest a = d >= 1 && a0 `mod` d /= 0
  where
    (lins,factors) = partition ((==1).fst) $ linerizel a
    a0 = case lins of [] -> 0; [(_,a)] -> -a
    d = if factors == [] then 0 else foldr1 gcd $ map snd factors
