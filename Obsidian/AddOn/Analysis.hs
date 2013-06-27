{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis (insertAnalysis, printAnalysis) where

import Obsidian.CodeGen.Program
import Obsidian
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian.AddOn.Analysis.Range
import Obsidian.AddOn.Analysis.Helpers

import Data.Word
import Data.Tuple
import Data.Int
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as M

instance ToProgram (Inputs,ArraySizes,IM) where
  toProgram i a () = a

type instance InputList (Inputs,ArraySizes,IM) = () 

printAnalysis :: ToProgram prg => prg -> InputList prg -> IO ()
printAnalysis p a = quickPrint (ins, sizes, insertAnalysis ins (strace sizes) im) ()
    where (ins,sizes,im) = toProgram 0 p a

insertAnalysis :: Inputs -> ArraySizes -> IM -> IM
insertAnalysis ins inSizes im = traverseComment (map Just . fst . snd) im2
  where inConstSizes = [(n,l) | (n,Left l) <- inSizes]
        sizes = M.fromList $ inConstSizes ++ collectIM getSizesIM im
        (Left threadBudget) = numThreads im

        im1,im2,im3 :: IMList ([String], M.Map (Exp Word32) (Word32, Word32))
        im1 = mapDataIM (([],).makeRanges.snd) $ insertCondsIM conds im
          where conds = condRange (ThreadIdx X, fromIntegral threadBudget)
                condRange (v,e) = [v <* e, v >=* 0]
        im1' = insertStringsIM (map (\(n,e,cs) -> 
          Just (show $ (n,M.lookup n sizes,M.assocs cs))).getIndicesIM) im1

        im2 = insertStringsIM (map (inRange sizes).getIndicesIM) im1
        im3 = insertStringsIM (map (inRange sizes).getIndicesIM) im2

insertStringsIM :: ((Statement ([String], t), t) -> [Maybe String])
                -> IMList ([String], t) -> IMList ([String], t)
insertStringsIM f = mapIM g
  where g (statement,(ss,cs)) = (ss ++ catMaybes (f (statement,cs)), cs)

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

-- Coalesced

--analyzeMemory :: GProgram () -> Int
--analyzeMemory p = 
--  let compiledP = compile p -- allocate memory

