{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.Dependency.Analysis (insertAnalysis, printAnalysis) where

--import qualified Obsidian.CodeGen.Program as P
import Obsidian.CodeGen.Program
import Obsidian
import Obsidian.Globs
import Obsidian.Dependency.ExpAnalysis
import Obsidian.Dependency.Helpers
import Obsidian.Dependency.Range
import Obsidian.Dependency.Coalesced
import Obsidian.Dependency.Cost
import Obsidian.Dependency.Hazards

import Data.Word
import Data.Tuple
import Data.Int
import Data.List
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
insertAnalysis ins inSizes im = traverseComment (map Just . getComments . snd) imF
                        -- ++ [(SComment (show $ M.assocs sizes),())]
                        ++ [(SComment "Depth:\t  Work:\tType:\tTotal cost:",())]
                        ++ map (\s -> (SComment s,())) (showCost cost)
                        ++ map (\s -> (SComment ("Hazard: " ++ show s),())) hazardEdges
                        -- ++ map (\s -> (SComment ("DepEdges: " ++ show s),())) depEdgesF
                        -- ++ map (\s -> (SComment ("Accesses: " ++ show s),())) (M.elems accesses)
                        -- ++ [(SComment $ show $ getOutputs im,())]
  where (inScalars,inConstSizes) = mapFst (map fst)
                                 $ partition ((==0).snd)
                                   [(n,l) | (n,Left l) <- inSizes]
        sizes = M.fromList $ inConstSizes ++ collectIM getSizesIM im
        threadBudget = case numThreads im of
          Left tb -> tb
          Right tb -> error ("nonconstant threadbudget: " ++ show tb)

        outs = error $ show $ getOutputs im

        im1, im2, imF :: IMList IMData
        im1 = mapDataIM (collectIMData.snd) $ insertIMCollection threadBudget inScalars im
        (im2,instructions) = traverseIMaccDataPre instructionNumbering [] im1
        imF = foldr (.) id (Prelude.reverse imActions) im2

        imActions :: [IMList IMData -> IMList IMData]
        imActions = [id
          , insertStringsIM "Out-of-bounds" $ map (inRange sizes).getIndicesIM
          , insertStringsCostIM "Coalesce"  $ map isCoalesced.getIndicesIM
          , insertStringsIM "Diverging"     $ diverges
          , insertStringsIM "Instruction"   $ (:[]) . liftM show . mfilter (>=0) . Just . getInstruction . snd
          , insertStringsIM "Hazards"       $ insertEdges accesses hazardEdges
          , insertStringsIM "Unnessary sync"$ unneccessarySyncs instructions accesses depEdgesF
          , mapIM $ \(p,d) -> insertCost (p,d)
          -- , insertStringsIM "Cost"    $ \(p,d) -> if getCost d /= noCost then [Just $ showCost (getCost d)] else []
          -- , insertStringsIM "Factors" $ \(p,d) -> [Just $ show (getSeqLoopFactor d, getParLoopFactor d)]
          ]

        cost = sumCost $ collectIM (list.getCost.snd) imF
        accesses = M.fromList
                 $ map (\a@(_,_,_,_,i) -> (i,a))
                 $ concat
                 $ map getAccessesIM instructions
        depEdges1 = makeFlowDepEdges im2
        depEdgesF = eliminateIndependent accesses depEdges1
        hazardEdges = keepHazards accesses depEdgesF

insertStringsIM :: String -> ((Statement IMData, IMData) -> [Maybe String])
                -> IMList IMData -> IMList IMData
insertStringsIM s f = mapIM g
  where g (statement,d) = addComments d $ map ((s++": ")++) $ catMaybes $ f (statement,d)
                               

insertStringsCostIM :: String
                    -> ((Statement IMData, IMData) -> [(CostT, Maybe String)])
                    -> IMList IMData -> IMList IMData
insertStringsCostIM s f = mapIM g
  where g (statement,d0) = d2
          where (costs,strings) = unzip $ f (statement,d0)
                d1 = addIMCostT d0 (sumCostT costs)
                d2 = addComments d1 $ map ((s++": ")++) $ catMaybes $ strings



traverseComment :: ((Statement a,a) -> [Maybe String]) -> IMList a -> IMList ()
traverseComment f = mapDataIM (const ()) . traverseIM makeComment
  where makeComment a = map (\s -> (SComment s,undefined))
                            (catMaybes $ f a)
                    ++ [a]

input1 :: DPull  EInt 
input1 = namedGlobal "apa" (variable "X")

t0 = printAnalysis (pushN 32 . fmap (+1). ixMap (+5)) (input1 :- ())


-- Hazards

-- Memory

-- creating IMData

data IMDataCollection = CRange (Exp Word32) (Exp Word32, Exp Word32)
                      | CCond  (Exp Bool)
                      | CThreadConstant (Exp Word32) --more advanced analysis needed here
                      | CLoop LoopType (Exp Word32)

type Conds = [(Exp Bool)]

insertIMCollection :: Word32 -> [Name] -> IMList a -> IMList (a,[IMDataCollection])
insertIMCollection bs inScalars = traverseIMaccDown (list `comp2` ins) start
  where
    ins :: [IMDataCollection] -> (Statement a,a) -> ((Statement a,(a,[IMDataCollection])),[IMDataCollection])
    ins cs b@(SCond          e l,a) = (mapSnd (,cs) b, cs ++ [CCond e])
    ins cs b@(SFor t nn pl   e l,a) = (mapSnd (,cs) b ,cs
                                        ++ collRange (variable nn)  e
                                        -- ++ [CThreadConstant (variable n)] -- not sure
                                        ++ [CLoop t (variable nn)])
    --ins cs b@(SSeqWhile     e l,a) = (mapSnd (,cs) b
    --                                 ,cs ++ [CCond e]
    --                                     ++ [CLoopSeq 2])
    ins cs b =                       (mapSnd (,cs) b,cs)

    start = collRange (ThreadIdx X) (fromIntegral bs)
         -- ++ [CLoopPar (ThreadIdx X)]
         ++ map (CThreadConstant . variable) inScalars
    collRange v e = [CRange v (0,e-1)]


collectIMData :: [IMDataCollection] -> IMData
collectIMData dc = IMDataA []
                           (M.fromListWith min $ catMaybes uppers)
                           (M.fromListWith max $ catMaybes lowers)
                           (S.fromList $ catMaybes $ map getBlockConsts dc)
                           noCost
                           loops
                           (-1)
  where
    getBlockConsts (CThreadConstant e) = Just e
    getBlockConsts _                   = Nothing

    loops = catMaybes $ map getLoopFactors dc
    getLoopFactors (CLoop Seq e) = Just $ (e,False)
    getLoopFactors (CLoop Par e) = Just $ (e,True)
    getLoopFactors _                  = Nothing

    (lowers,uppers) = unzip
                    $ map (\(e,(l,u)) -> (fmap (e,) l
                                         ,fmap (e,) u))
                    $ concat
                    $ map makeRange dc

    makeRange :: IMDataCollection -> [(Exp Word32, (Maybe Integer, Maybe Integer))]
    makeRange (CRange e (l,h)) = [(e, (expToMaybe $ Just l,expToMaybe $ Just h))]
    makeRange (CCond e) = map (\(e,(l,h)) -> (e,(l,h))) $ makeRangeE e
    makeRange _ = []


    makeRangeE :: Exp Bool -> [(Exp Word32, (Maybe Integer, Maybe Integer))]
    makeRangeE (BinOp o a b) = makeRangeB (witness a) o a b
    makeRangeE _ = []
    makeRangeB :: Witness a -> (Op ((a,b) -> Bool)) -> Exp a -> Exp b
               -> [(Exp Word32, (Maybe Integer, Maybe Integer))]
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
             -> [(Exp Word32, (Maybe Integer,Maybe Integer))]
    makeInEq a f = map solToRange $ solveIneq a
      where solToRange (var,val,left) =
              if left
                then (var,mapPair expToMaybe $        f val)
                else (var,mapPair expToMaybe $ swap $ f val)
    expToMaybe (Just (Literal a)) = Just $ fromIntegral a
    expToMaybe _                  = Nothing

    solveIneq :: Exp Word32 -> [(Exp Word32, Exp Word32, Bool)]
    solveIneq x = [(e, move p $ M.delete e m, p >= 0)
                  | (e,p) <- M.assocs m, p/=0, e/=1]
      where m = linerize x
            --solves p*e+a <> 0 => e <> -a/p
            move p a = (-(unLinerize a)) `div` fromIntegral (abs p)

instructionNumbering :: ((Statement IMData, IMData), [(Statement IMData,IMData)])
                     -> (IMData, [(Statement IMData,IMData)])
instructionNumbering ((p,d),il) =
  case shouldCount of
    Just p' -> let d' = setInstruction d (length il)
               in (d', il++[(p',d')])
    Nothing -> (d,il)
  where shouldCount :: Maybe (Statement IMData)
        shouldCount = case p of
            SAssign n l e -> Just $ SAssign n l e
            SSynchronize  -> Just SSynchronize
            _             -> Nothing

