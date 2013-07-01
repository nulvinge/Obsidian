{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis (insertAnalysis, printAnalysis) where

--import qualified Obsidian.CodeGen.Program as P
import Obsidian.CodeGen.Program
import Obsidian
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian.AddOn.Analysis.Helpers
import Obsidian.AddOn.Analysis.Range
import Obsidian.AddOn.Analysis.Coalesced
import Obsidian.AddOn.Analysis.Cost

import Data.Word
import Data.Tuple
import Data.Int
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S

instance ToProgram (Inputs,ArraySizes,IM) where
  toProgram i a () = a

type instance InputList (Inputs,ArraySizes,IM) = () 

printAnalysis :: ToProgram prg => prg -> InputList prg -> IO ()
printAnalysis p a = quickPrint (ins, sizes, insertAnalysis ins sizes im) ()
    where (ins,sizes,im) = toProgram 0 p a

insertAnalysis :: Inputs -> ArraySizes -> IM -> IM
insertAnalysis ins inSizes im = traverseComment (map Just . fst . snd) im2
                        ++ [(SComment (show $ M.assocs sizes),())]
                        ++ [(SComment ("Total cost:" ++ showCost cost),())]
  where inConstSizes = [(n,l) | (n,Left l) <- inSizes]
        sizes = M.fromList $ inConstSizes ++ collectIM getSizesIM im
        (Left threadBudget) = numThreads im

        im1, im2 :: IMList ([String], IMData)
        im1 = mapDataIM (([],).collectIMData.snd) $ insertIMCollection threadBudget im
        im2 = foldr (.) id (Prelude.reverse imActions) im1

        imActions :: [(IMList ([String], IMData) -> IMList ([String], IMData))]
        imActions =
          [ insertStringsIM "Out-of-bounds" $ map (inRange sizes).getIndicesIM
          , insertStringsCostIM "Coalesce"      $ map isCoalesced.getIndicesIM
          , mapIM $ \(p,(e,d)) -> (e,) $ insertCost (p,d)
          , insertStringsIM "Cost"    $ \(p,d) -> if getCost d /= noCost then [Just $ showCost (getCost d)] else []
          --, insertStringsIM "Factors" $ \(p,d) -> [Just $ show (getSeqLoopFactor d, getParLoopFactor d)]
          ]

        cost = sumCost $ collectIM (list.getCost.snd.snd) im2

insertStringsIM :: String -> ((Statement ([String], t), t) -> [Maybe String])
                -> IMList ([String], t) -> IMList ([String], t)
insertStringsIM s f = mapIM g
  where g (statement,(ss,d)) = (ss ++ map ((s++": ")++)
                                          (catMaybes (f (statement,d)))
                                ,d)

insertStringsCostIM :: String
                    -> ((Statement ([String], IMData), IMData) -> [(CostT, Maybe String)])
                    -> IMList ([String], IMData) -> IMList ([String], IMData)
insertStringsCostIM s f = mapIM g
  where g (statement,(ss,cs)) = (ss ++ map ((s++": ")++) (catMaybes $ strings)
                                ,addIMCostT cs (sumCostT costs))
          where (costs,strings) = unzip $ f (statement,cs)


traverseComment :: ((Statement a,a) -> [Maybe String]) -> IMList a -> IMList ()
traverseComment f = mapDataIM (const ()) . traverseIM makeComment
  where makeComment a = map (\s -> (SComment s,undefined))
                            (catMaybes $ f a)
                    ++ [a]

input1 :: DPull  EInt 
input1 = namedGlobal "apa" (variable "X")

t0 = printAnalysis (pushGrid 32 . fmap (+1). ixMap (+5)) (input1 :- ())


-- Hazards

-- Memory

-- creating IMData

data IMDataCollection = CRange (Exp Word32) (Exp Word32, Exp Word32)
                      | CCond  (Exp Bool)
                      | CThreadConstant (Exp Word32) --more advanced analysis needed here
                      | CLoopSeqFactor (Exp Word32)
                      | CLoopParFactor (Exp Word32)

type Conds = [(Exp Bool)]

insertIMCollection :: Word32 -> IMList a -> IMList (a,[IMDataCollection])
insertIMCollection bs = traverseIMacc (ins) start
  where
    ins :: [IMDataCollection] -> (Statement a,a) -> [(Statement a,(a,[IMDataCollection]),[IMDataCollection])]
    ins cs (SCond           e l,a) = [(SCond          e l, (a,cs), cs ++ [CCond e])]
    ins cs (SSeqFor n       e l,a) = [(SSeqFor n      e l, (a,cs), cs ++ collRange (variable n)  e
                                                                      ++ [CThreadConstant (variable n)]
                                                                      ++ [CLoopSeqFactor (variable n)])]
    ins cs (SSeqWhile       e l,a) = [(SSeqWhile      e l, (a,cs), cs ++ [CCond e]
                                                                      ++ [CLoopSeqFactor 2])]
    ins cs (SForAll         e l,a) = [(SForAll        e l, (a,cs), cs ++ collRange (ThreadIdx X) e)]
                                                                      -- ++ [CLoopParFactor (ThreadIdx X)])]
    ins cs (SForAllBlocks   e l,a) = [(SForAllBlocks  e l, (a,cs), cs ++ collRange (BlockIdx X)  e
                                                                      ++ [CThreadConstant (BlockIdx X)]
                                                                      ++ [CLoopParFactor (BlockIdx X)])]
    ins cs (b,a) = [(b,(a,cs),cs)]

    start = collRange (ThreadIdx X) (fromIntegral bs)
         ++ [CLoopParFactor (ThreadIdx X)]
    collRange v e = [CRange v (0,e-1)]


collectIMData :: [IMDataCollection] -> IMData
collectIMData dc = IMDataA (M.fromListWith min $ catMaybes uppers)
                           (M.fromListWith max $ catMaybes lowers)
                           (S.fromList $ catMaybes $ map getBlockConsts dc)
                           noCost
                           seqs
                           pars
  where
    getBlockConsts (CThreadConstant e) = Just e
    getBlockConsts _                   = Nothing

    (seqs,pars) = partitionEithers $ catMaybes $ map getLoopFactors dc
    getLoopFactors (CLoopSeqFactor e) = Just $ Left  e
    getLoopFactors (CLoopParFactor e) = Just $ Right e
    getLoopFactors _                  = Nothing

    (lowers,uppers) = unzip
                    $ map (\(e,(l,u)) -> (fmap (e,) l
                                         ,fmap (e,) u))
                    $ concat
                    $ map makeRange dc

    makeRange :: IMDataCollection -> [(Exp Word32, (Maybe Word32, Maybe Word32))]
    makeRange (CRange e (l,h)) = [(e, (expToMaybe $ Just l,expToMaybe $ Just h))]
    makeRange (CCond e)     = map (\(e,(l,h)) -> (e,(l,h))) $ makeRangeE e
    makeRange _ = []


    makeRangeE :: Exp Bool -> [(Exp Word32, (Maybe Word32, Maybe Word32))]
    makeRangeE (BinOp o a b) = makeRangeB (witness a) o a b
    makeRangeE _ = []
    makeRangeB :: Witness a -> (Op ((a,b) -> Bool)) -> Exp a -> Exp b
               -> [(Exp Word32, (Maybe Word32, Maybe Word32))]
    makeRangeB Word32Witness Eq  a b = makeInEq (a-b)  $ \v -> (Just v, Just v)
    makeRangeB Word32Witness Lt  a b = makeInEq (a-b+1)$ \v -> (Nothing,Just v)
    makeRangeB Word32Witness LEq a b = makeInEq (a-b)  $ \v -> (Nothing,Just v)
    makeRangeB Word32Witness Gt  a b = makeInEq (a-b-1)$ \v -> (Just v,Nothing)
    makeRangeB Word32Witness GEq a b = makeInEq (a-b)  $ \v -> (Just v,Nothing)
    makeRangeB BoolWitness And a b = makeRangeE a ++ makeRangeE b
    makeRangeB _ _ _ _ = []

    minmax (a1,b1,c1) (a2,b2,c2) = (mergeMaybies max a1 a2, mergeMaybies min b1 b2, c1||c2)
    mergeMaybies f a b = case catMaybes [a,b] of
                          []    -> Nothing
                          [a]   -> Just a
                          [a,b] -> Just $ f a b
    maybeRange (Just a, Just b, s) = Just (a, b, s)
    maybeRange _                   = Nothing

    makeInEq :: Exp Word32
             -> (Exp Word32 -> (Maybe (Exp Word32), Maybe (Exp Word32)))
             -> [(Exp Word32, (Maybe Word32,Maybe Word32))]
    makeInEq a f = map solToRange $ solveIneq a
      where solToRange (var,val,left) =
              if left
                then (var,mapPair expToMaybe $        f val)
                else (var,mapPair expToMaybe $ swap $ f val)
    expToMaybe (Just (Literal a)) = Just a
    expToMaybe _                  = Nothing

    solveIneq :: Exp Word32 -> [(Exp Word32, Exp Word32, Bool)]
    solveIneq x = [(e, move p $ M.delete e m, p >= 0)
                  | (e,p) <- M.assocs m, p/=0, e/=1]
      where m = linerize x
            --solves p*e+a <> 0 => e <> -a/p
            move p a = (-(unLinerize a)) `div` fromIntegral (abs p)

