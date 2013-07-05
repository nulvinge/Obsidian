{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Hazards (insertHazards, makeFlowDepEdges, eliminateDepEdges)  where

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

listProduct :: [a] -> [b] -> [(a,b)]
listProduct la lb = [(a,b) | a <- la, b <- lb]
combinations :: [a] -> [(a,a)]
combinations l = concat $ map (\(i,ll) -> map (i,) ll) $ zip l (prefixes l)
prefixes :: [a] -> [[a]]
prefixes l = map (`L.take` l) $ L.take (length l) [0..]

isIndependent :: Access -> Access -> Maybe String
isIndependent aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi)
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
            (d0,ds) = fromJust mds
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
            same = ai == bi
            local = isLocal an && isLocal bn

sameWarp :: Access -> Access -> Bool
sameWarp aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi)
  | ad `sameWarpRange` bd && rangeSize (warprange ad) <= 32 = True
  | otherwise = False --needs better analysis

rangeSize (l,h) = h-l

warprange d = mapPair (*warpsize) (tl `div` warpsize, (th+1)`cdiv`warpsize)
  where Just (tl,th) = getRange d (ThreadIdx X)
sameWarpRange d1 d2 = mapPair2 (==) (warprange d1) (warprange d2) == (True,True)

banerjee aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) = maybe False (0>) h
                                                || maybe False (>0) l
  where
    (al,ah) = getRangeM ad a
    (bl,bh) = getRangeM bd b
    (l,h) = (liftM2 (-) al bh,liftM2 (-) ah bl)

diffs aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) = do
  guard $ getLoops ad == getLoops bd
  (c0,afs,bfs) <- getFactors2 aa ba
  return (c0
         , map (\((e,sp,a),(_,_,b)) -> (e,(sp,a,b))) $ zip afs bfs)

getFactors2 :: Access -> Access -> Maybe (Integer, [(Exp Word32,Bool,Integer)], [(Exp Word32,Bool,Integer)])
getFactors2 aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) = do
    guard $ 0 == (M.size $ linerize $ unLinerizel a0v - unLinerizel b0v)
    return (a0-b0,af,bf)
  where (a0,af,a0v) = getFactors ad a
        (b0,bf,b0v) = getFactors bd b
        isConst e = getBlockConstant ad e && getBlockConstant bd e


getFactors :: IMData -> Exp Word32 -> (Integer, [(Exp Word32,Bool,Integer)], [(Exp Word32,Integer)])
getFactors d e = (sum consts, factors, nonLoopConst)
  where e' = linerize e
        factors = map (\(f,ps) -> (f,ps,M.findWithDefault 0 f e')) $ getLoops d
        (consts,nonconsts) = partitionMaybes (\(k,n) -> liftM (n*) $ getConst k)
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


type DepEdge = ((Int,Int),(Int,Int),[DepEdgeType], [Exp Bool])
data DepEdgeType = SyncDepEdge
                 | WarpDepEdge
                 | BlockDepEdge
                 | ThreadDepEdge
                 | DataDep [(Direction,(Exp Word32,Bool))]
  deriving (Show,Eq)

data Direction = DAny | DEqual | DLess | DMore
  deriving (Show,Eq)

--thid does not handle synchronization within loops yet
makeFlowDepEdges :: IMList IMData -> [DepEdge]
makeFlowDepEdges = map (\((a,b,c),t) -> (a,b,t,c))
                 . M.toList 
                 . M.fromListWith (++)
                 . map (\(a,b,t,c)->((a,b,c),t))
                 . nub
                 . (\(_,(_,_,globs,a)) -> processGlobals (strace globs) ++ a)
                 . traverseIMaccDataPrePost pre post ([],[],[],[])
  where
    pre :: ((Statement IMData, IMData), ([Access], [Access], [Access], [DepEdge]))
        -> (IMData, ([Access], [Access], [Access], [DepEdge]))
    pre ((SSynchronize, d),(loc,prevloc,glob,edges)) = (d,([],prevloc++loc,glob,edges))
    pre ((p,d),            (loc,prevloc,glob,edges)) = (d,
        (loc++local,prevloc,glob++global,edges++newedges))
      where (local,global) = partition (isLocal. \(n,_,_,_,_)->n) $ getAccessesIM (p,d)
            newedges = concat $ [makeEdges [] True True  (a,b) | a <- local, b <- prevloc]
                             ++ [makeEdges [] True False (a,b) | a <- local, b <- loc]
                             ++ [makeEdges [] True False (a,a) | a <- local]
                             ++ [makeEdges [] True False (a,b) | (a,b) <- combinations local]
    post ((p, d),(loc,prevloc,glob,edges)) = (d,(loc,prevloc,glob,edges))
    processGlobals gs = concat $ [makeEdges [] False False (a,b) | (a,b) <- combinations gs]
                              ++ [makeEdges [] True False (a,a) | a <- gs]

makeEdges :: [Exp Bool] -> Bool -> Bool -> (Access,Access) -> [DepEdge]
makeEdges conds local nosync (aa@(an,a,arw,ad,ai),ba@(bn,b,brw,bd,bi))
  | an /= bn   = [] --different arrays
  | arw && brw = [] --read read
  | otherwise  = [(ai, bi, [DataDep $ map (DAny,) $ getLoops ad], conds)]
       ++(if not (local && nosync) then []
            else [(ai, bi, [SyncDepEdge], conds)]
      {- )++(if not (sameThread && sameTBGroup) then []
            else [(ai, bi, [ThreadDepEdge], conds)]
      )++(if sameThread || not (aa `sameWarp` ba && not sameTBGroup) then []
            else [(ai, bi, [WarpDepEdge], conds)]
      )++(if not sameBlock then []
            else [(ai, bi, [BlockDepEdge], conds)]
      -}
      )
  where mds = aa `diffs` ba
        (d0,ds) = fromJust mds
        sameThread = sameGroup (ThreadIdx X)
        sameBlock  = sameGroup (BlockIdx  X)
        sameTBGroup = sameThread && (local || sameBlock)
        sameGroup e = isJust mds && d0 == 0 &&
                    (  (af == bf && af /= 0)
                    || (getRange ad e == Just (0,0)))
          where (_,af,bf) = fromMaybe (undefined,0,0) $ lookup e ds

eliminateDepEdges :: [Access] -> [DepEdge] -> [DepEdge]
eliminateDepEdges accesses edges = catMaybes $ map tryEdge edges
  where
    aMap = M.fromList $ map (\a@(_,_,_,_,i) -> (i,a)) accesses
    tryEdge (a',b',t,c) = if isJust (isIndependent aa ba)
        then Just (a',b',t,c)
        else Nothing
      where aa@(an,a,arw,ad,ai) = fromJust $ M.lookup a' aMap
            ba@(bn,b,brw,bd,bi) = fromJust $ M.lookup b' aMap

insertHazards :: [Access] -> [DepEdge] -> (Statement IMData,IMData) -> [Maybe String]
insertHazards accesses edges (p,d) = map hazardEdge
                                   $ filter (\((i,_),_,_,_) -> i == getInstruction d)
                                   $ edges
  where
    aMap = M.fromList $ map (\a@(_,_,_,_,i) -> (i,a)) accesses
    hazardEdge (a',b',t,c)
      | elem SyncDepEdge t && local = Nothing
      | not same && (sameThread || aa `sameWarp` ba) = Nothing
      | otherwise = Just $ "with " ++ show b' ++ loc sameThread
      where aa@(an,a,arw,ad,ai) = fromJust $ M.lookup a' aMap
            ba@(bn,b,brw,bd,bi) = fromJust $ M.lookup b' aMap

            mds = aa `diffs` ba
            (d0,ds) = fromJust mds
            sameThread = sameGroup (ThreadIdx X)
            sameBlock  = sameGroup (BlockIdx  X)
            sameTBGroup = sameThread && (local || sameBlock)
            sameGroup e = isJust mds && d0 == 0 &&
                        (  (af == bf && af /= 0)
                        || (getRange ad e == Just (0,0)))
              where (_,af,bf) = fromMaybe (undefined,0,0) $ lookup e ds
            loc True                 = ": same thread dependence"
            loc _ | aa `sameWarp` ba = ": same warp dependence"
            loc _                    = ""
            same = ai == bi
            local = isLocal an && isLocal bn

