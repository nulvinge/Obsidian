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
insertAnalysis ins inSizes im = traverseComment (map Just . fst . snd) im3
                        ++ [(SComment (show $ M.assocs sizes),())]
                        ++ [(SComment ("Total cost:" ++ show cost),())]
  where inConstSizes = [(n,l) | (n,Left l) <- inSizes]
        sizes = M.fromList $ inConstSizes ++ collectIM getSizesIM im
        (Left threadBudget) = numThreads im

        imd = mapDataIM (collectIMData.snd) $ insertIMCollection threadBudget im
        (imc, cost) = insertCost imd
        im1 = mapDataIM (\d -> (if getCost d > 0 then ["Cost:" ++ show (getCost d)] else [], d)) imc

        im1,im2,im3 :: IMList ([String], IMData)
        im2 = insertStringsIM "Out-of-bounds" (map (inRange sizes).getIndicesIM) im1
        im3 = insertStringsIM "Coalesce"    (map isCoalesced.getIndicesIM) im2

insertStringsIM :: String -> ((Statement ([String], t), t) -> [Maybe String])
                -> IMList ([String], t) -> IMList ([String], t)
insertStringsIM s f = mapIM g
  where g (statement,(ss,cs)) = (ss ++ map ((s++": ")++)
                                           (catMaybes (f (statement,cs)))
                                ,cs)

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

-- Cost model

-- creating IMData

data IMDataCollection = CRange (Exp Word32) (Exp Word32, Exp Word32)
                      | CCond  (Exp Bool)
                      | CThreadConstant (Exp Word32) --more advanced analysis needed here

type Conds = [(Exp Bool)]

insertIMCollection :: Word32 -> IMList a -> IMList (a,[IMDataCollection])
insertIMCollection bs = traverseIMacc (ins) (collRange (ThreadIdx X) (fromIntegral bs))
  where
    ins :: [IMDataCollection] -> (Statement a,a) -> [(Statement a,(a,[IMDataCollection]),[IMDataCollection])]
    ins cs (SCond           e l,a) = [(SCond          e l, (a,cs), cs ++ [CCond e])]
    ins cs (SSeqFor n       e l,a) = [(SSeqFor n      e l, (a,cs), cs ++ collRange (variable n)  e
                                                                      ++ [CThreadConstant (variable n)])]
    ins cs (SSeqWhile       e l,a) = [(SSeqWhile      e l, (a,cs), cs ++ [CCond e])]
    ins cs (SForAll         e l,a) = [(SForAll        e l, (a,cs), cs ++ collRange (ThreadIdx X) e)]
    ins cs (SForAllBlocks   e l,a) = [(SForAllBlocks  e l, (a,cs), cs ++ collRange (BlockIdx X)  e
                                                                      ++ [CThreadConstant (BlockIdx X)])]
    ins cs (b,a) = [(b,(a,cs),cs)]
    collRange v e = [CRange v (0,e-1)]


collectIMData :: [IMDataCollection] -> IMData
collectIMData dc = IMDataA (M.fromListWith max $ catMaybes lowers)
                           (M.fromListWith min $ catMaybes uppers)
                           (S.fromList $ catMaybes blockconsts)
                           0
  where
    (lowers,uppers,blockconsts) = unzip3
                                $ map (\(e,(l,u,b)) -> (fmap (e,) l
                                                       ,fmap (e,) u
                                                       ,boolToMaybe b e))
                                $ concat
                                $ map makeRange dc

    makeRange :: IMDataCollection -> [(Exp Word32, (Maybe Word32, Maybe Word32, Bool))]
    makeRange (CRange e (l,h)) = [(e, (expToMaybe $ Just l,expToMaybe $ Just h,False))]
    makeRange (CCond e)     = map (\(e,(l,h)) -> (e,(l,h,False))) $ makeRangeE e
    makeRange (CThreadConstant e) = [(e,(Nothing, Nothing, True))]


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

