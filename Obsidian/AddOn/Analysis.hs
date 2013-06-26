{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis (insertAnalysis, printAnalysis) where

import qualified Obsidian.CodeGen.CUDA as CUDA
import Obsidian.CodeGen.Program
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian
import Obsidian.Globs
import Obsidian.AddOn.ExpAnalysis
import Data.Tuple (swap)

import Data.Word
import Data.Tuple
import Data.Int
import Data.Maybe
import Data.Either
import Control.Monad

import qualified Data.Map as M
import Debug.Trace

instance ToProgram (Inputs,ArraySizes,IM) where
  toProgram i a () = a

type instance InputList (Inputs,ArraySizes,IM) = () 

-- Coalesced

quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input 

printAnalysis :: ToProgram prg => prg -> InputList prg -> IO ()
printAnalysis p a = quickPrint (ins, sizes, insertAnalysis ins (strace sizes) im) ()
    where (ins,sizes,im) = toProgram 0 p a

strace a = trace (show a) a

insertAnalysis :: Inputs -> ArraySizes -> IM -> IM
insertAnalysis ins inSizes im = im'
  ++ out (SComment $ "test" ++ show (length im, length im'))
  where inConstSizes = [(n,l) | (n,Left l) <- inSizes]
        sizes = M.fromList $ inConstSizes ++ collectIM getSizesIM im
        (Left threadBudget) = numThreads im
        im1 :: IMList (M.Map (Exp Word32) (Word32, Word32))
        im1 = mapDataIM (makeRanges.snd) $ insertCondsIM conds im
          where conds = condRange (ThreadIdx X, fromIntegral threadBudget)
                condRange (v,e) = [v <* e, v >=* 0]
        im1' = traverseComment (map (\(n,e,cs) -> Just (show $ (n,M.lookup n sizes,M.assocs cs))).getIndicesIM) im1
        im' = traverseComment (map (inRange sizes).getIndicesIM) im1

makeRanges :: Conds -> M.Map (Exp Word32) (Word32, Word32)
makeRanges = M.mapMaybe maybeRange . M.fromListWith minmax . concat . strace . map makeRange
  where
    makeRange :: Exp Bool -> [(Exp Word32, (Maybe Word32, Maybe Word32))]
    makeRange (BinOp o a b) = makeRangeB (witness a) o a b
    makeRange _ = []
    makeRangeB :: Witness a -> (Op ((a,b) -> Bool)) -> Exp a -> Exp b
               -> [(Exp Word32, (Maybe Word32, Maybe Word32))]
    makeRangeB Word32Witness Eq  a b = makeInEq (a-b)  $ \v -> (Just v, Just v)
    makeRangeB Word32Witness Lt  a b = makeInEq (a-b+1)$ \v -> (Nothing,Just v)
    makeRangeB Word32Witness LEq a b = makeInEq (a-b)  $ \v -> (Nothing,Just v)
    makeRangeB Word32Witness Gt  a b = makeInEq (a-b-1)$ \v -> (Just v,Nothing)
    makeRangeB Word32Witness GEq a b = makeInEq (a-b)  $ \v -> (Just v,Nothing)
    makeRangeB BoolWitness And a b = makeRange a ++ makeRange b
    makeRangeB _ _ _ _ = []

    minmax (a1,b1) (a2,b2) = (mergeMaybies max a1 a2, mergeMaybies min b1 b2)
    mergeMaybies f a b = case catMaybes [a,b] of
                          []    -> Nothing
                          [a]   -> Just a
                          [a,b] -> Just $ f a b
    maybeRange (Just a, Just b) = Just (a,b)
    maybeRange _                = Nothing

    makeInEq :: Exp Word32
             -> (Exp Word32 -> (Maybe (Exp Word32), Maybe (Exp Word32)))
             -> [(Exp Word32, (Maybe Word32,Maybe Word32))]
    makeInEq a f = map solToRange $ solveIneq a
      where solToRange (var,val,left) =
              if left
                then (var,mapPair expToMaybe $        f val)
                else (var,mapPair expToMaybe $ swap $ f val)
            mapPair f (a,b) = (f a, f b)
            expToMaybe (Just (Literal a)) = Just a
            expToMaybe _                  = Nothing

    solveIneq :: Exp Word32 -> [(Exp Word32, Exp Word32, Bool)]
    solveIneq x = [(e, move p $ M.delete e m, p >= 0)
                  | (e,p) <- M.assocs m , p/=0 , e/=1]
      where m = linerize x
            move p a = (-(unLinerize a)) `div` fromIntegral (abs p)


inRange sizes (n,e,cs) =
  if isNothing size
    then Just $ "no size info about " ++ n
    else if any isNothing ranges
      then if outofrange
        then Just "probbably out of range"
        else Just $ "indeterminate because " ++ (show $ catMaybes indets)
                ++ " has no range"
      else if outofrange
        then Just $ "definatly out of range: " ++ (show range)
                ++ " does not fit in " ++ n ++ " with size " ++ (show size)
        else Nothing
  where ranges = map (\(e,v) -> getRange cs e >>= pairMul v) $ M.assocs (linerize e)
        pairMul a (l,h) = Just (l*a,h*a)
        size = M.lookup n sizes 
        range = let (l,h) = unzip $ catMaybes ranges
                in (sum l,sum h)
        outofrange = (fst range < 0) || (fromJust size <= snd range)
        indets = map (\(e,v) -> if isNothing (getRange cs e) then Just (e,cs) else Nothing) $ M.assocs (linerize e)

getRange :: (Num a, Ord a, Scalar a) => M.Map (Exp a) (a,a) -> Exp a -> Maybe (a,a)
getRange = gr
  where
    gr :: (Num a, Ord a, Scalar a) => M.Map (Exp a) (a,a) -> Exp a -> Maybe (a,a)
    gr r (BinOp Add a b) = bop r a b $ \al ah bl bh -> return (al+bl,ah+bh)
    gr r (BinOp Sub a b) = bop r a b $ \al ah bl bh -> return (al-bh,ah-bl)
    gr r (BinOp Mul a b) = bop r a b $ \al ah bl bh -> return (al*bl,ah*bh)
    gr r (BinOp Div a b) = bop r a b $ \al ah bl bh -> guard (bl==bh) >> return (al`div`bh,ah`div`bl)
    gr r (BinOp Mod a b) = bop r a b $ \al ah bl bh -> guard (bl==bh) >> return (max al 0,min ah (bh-1))
    gr r (BinOp BitwiseXor a b) = bop r a b $ \al ah bl bh -> do
      guard (al >= 0 && bl >= 0)
      return (0,(getNext2Powerm ah `max` getNext2Powerm bh))
    gr r (Literal a) = Just (a,a)
    gr r a = M.lookup a r

    bop :: (Num a, Ord a, Scalar a)
        => M.Map (Exp a) (a,a) -> Exp a -> Exp a
        -> (a -> a-> a -> a -> Maybe (a,a)) -> Maybe (a,a)
    bop r a b f = do
      (al,ah) <- gr r a
      (bl,bh) <- gr r b
      f al ah bl bh


traverseComment :: ((Statement a,a) -> [Maybe String]) -> IMList a -> IMList ()
traverseComment f = mapDataIM (const ()) . traverseIM makeComment
  where makeComment a = map (\s -> (SComment s,undefined))
                            (catMaybes $ f a)
                    ++ [a]

input1 :: DPull  EInt 
input1 = namedGlobal "apa" (variable "X")

t0 = printAnalysis (pushGrid 32 . fmap (+1). ixMap (+5)) (input1 :- ())

collectIndices a = map (\(_,[r]) -> r) $ collectIndex a
  where collectIndex (Index r) = [r]
        collectIndex _ = []

linerize :: (Num a, Ord (Exp a)) => Exp a -> M.Map (Exp a) a
linerize = normalize . linerize'

linerize' :: (Num a) => Exp a -> [(a,Exp a)]
linerize' (BinOp Add a b) = linerize' a ++ linerize' b
linerize' (BinOp Sub a b) = linerize' a ++ (map (\(n,v) -> (-n,v)) $ linerize' b)
linerize' (BinOp Mul (Literal a) b) = map (\(n,v) -> (n*a,v)) $ linerize' b
linerize' (BinOp Mul a (Literal b)) = map (\(n,v) -> (n*b,v)) $ linerize' a
linerize' (Literal a)     = [(a, Literal 1)]
linerize' a@(ThreadIdx X) = [(1, ThreadIdx X)]
linerize' a@(BlockIdx X)  = [(1, BlockIdx X)]
linerize' a               = [(1,a)]

normalize :: (Num a, Ord (Exp a)) => [(a,Exp a)] -> M.Map (Exp a) a
normalize = M.fromListWith (+) . map swap

unLinerize :: (Scalar a, Integral a, Num a, Ord (Exp a)) => M.Map (Exp a) a -> Exp a
unLinerize x = sum [val * fromIntegral p | (val,p) <- M.assocs x]

isWarpConstant (Literal a) = True
isWarpConstant (ThreadIdx X) = False
isWarpConstant (BlockIdx X) = True



-- Hazards

-- Memory

--analyzeMemory :: GProgram () -> Int
--analyzeMemory p = 
--  let compiledP = compile p -- allocate memory

