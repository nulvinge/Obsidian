{-# LANGUAGE ScopedTypeVariables,
             GADTs,
             RankNTypes,
             ExistentialQuantification,
             MultiParamTypeClasses,
             FlexibleInstances,
             TypeFamilies,
             FlexibleContexts #-}

module Stages where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian.Program hiding (Bind,Return)
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Array
import Obsidian.Library
import Obsidian.Force
import Obsidian.CodeGen.InOut
import Obsidian.Atomic
import Debug.Trace

import Data.Word
import Data.Int
import Data.Bits
import Data.Maybe
import Data.List (genericIndex)

import qualified Data.Vector.Storable as V

import Control.Monad.State

import Prelude hiding (zipWith,sum,replicate)
import qualified Prelude as P

data Array a = Arr [a]

type Index = Exp Word32 -> Exp Word32

data BackStage a where
  FMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> [Index] -> [Index] -> [Index] -> Word32 -> BackStage a

type Stage a = [BackStage a]

data FrontStage a b where
  SFMap  :: (Scalar a) => ([Exp a] -> [Exp a]) -> [Index] -> [Index] -> FrontStage a ()
  Bind   :: FrontStage a b -> (b -> FrontStage a c) -> FrontStage a c
  Return :: b -> FrontStage a b
  Len    :: FrontStage a Word32
  Block  :: FrontStage a Word32

instance Monad (FrontStage a) where
  return = Return
  (>>=)  = Bind

run :: (Scalar a)
    => FrontStage a () -> Word32 -> Word32
    -> GlobPull (Exp a) -> GProgram (GlobPull (Exp a))
run a b n = runG s b n
  where (s,_,_,()) = mkStage b n [] a

mkStage :: (Scalar a)
        => Word32 -> Word32 -> [Index] -> FrontStage a b
        -> (Stage a, [Index], Word32, b)
mkStage _ 0 _ _ = error "Stage cannot have zero width"
mkStage 0 _ _ _ = error "Stage cannot have zero blocksize"
mkStage b n ob (SFMap f i o) = ([FMap f i o ob n], o, ni ,())
  where ni = n `div` fromIntegral (length i) * fromIntegral (length o)
mkStage b n ob (a `Bind` f) = (s1 ++ s2, ob2, n2, b2)
  where (s1,ob1,n1,b1) = mkStage b n ob a
        (s2,ob2,n2,b2) = mkStage b n1 ob1 (f b1)
mkStage b n ob (Return a)   = ([],ob,n,a)
mkStage b n ob (Len)        = ([],ob,n,n)
mkStage b n ob (Block)      = ([],ob,n,b)

instance Show (BackStage a) where
  show (FMap f i o ob nn) = "FMap f " ++ show (length i) ++ " " ++ show (length o) ++  " " ++ show (length ob)

accessA :: Word32 -> [Index] -> Word32 -> [Index] -> Bool
accessA divisions ob n i = (length arrWriteThreads) == (length arrReadThreads)
                        && all sameDivision (zip arrWriteThreads arrReadThreads)
  where arrWriteThreads = getIndices ob
        arrReadThreads  = getIndices i
        getIndices :: [Index] -> [Exp Word32]
        getIndices ixf = concat [[(ixf !! x) (fromIntegral ix)
                                 | x <- [0..(length ixf-1)]]
                                | ix <- [0..((n `div` (fromIntegral (length ixf)))-1)]]
        sameDivision (wt,rt) = isJust $ do
          w <- getConstant wt
          r <- getConstant rt
          guard $ (w `div` divisions) == (r `div` divisions)
        getConstant (Literal a) = Just a

runnable :: (Scalar a)
        => Word32 -> Stage a
        -> (Stage a, Stage a, Word32, Word32)
runnable divisions (a:as) = 
  case runnable' (a:as) of
    ([],_,_,_) -> ([tr1], as, tl1, tt1)
      where ([tr1],[],tl1,tt1) = single a
    a          -> a
  where runnable' :: (Scalar a)
                 => Stage a
                 -> (Stage a, Stage a, Word32, Word32)
        runnable' ao@(a@(FMap f i o ob nn) : as) =
            if null ob || {- nn <= divisions || -} accessA divisions ob nn i
                then if null as || (divisions == 1 && tt1 /= tt2) --special case
                        then single a
                        else (tr1 : tr2, tn2, tl2, tt1)
                else ([], ao, nn, 0)
            where ([tr1],[], tl1,tt1)  = single a
                  (tr2,tn2,tl2,tt2) = runnable' as
        single a@(FMap f i o ob nn) = ([a], [], nn`div`ni*no, nn`div`ni)
            where ni = fromIntegral (length i)
                  no = fromIntegral (length o)


runG :: (Scalar a)
     => Stage a -> Word32 -> Word32
     -> GlobPull (Exp a) -> GProgram (GlobPull (Exp a))
runG [] _ _ a = return a
runG ss b nn (GlobPull ixf) = do
    as <- rf
    runG tn b tl as
  where rf = cheat $ forceG $ GlobPush $ \wf -> do
                ForAllBlocks $ \bix -> do
                    Push _ pf <- runB False tr b bix (Pull nn ixf)
                    pf wf
        (tr, tn, tl, _) = runnable b ss

runB :: (Scalar a)
     => Bool -> Stage a -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
runB fromShared s b bix a = do
        a' <- runW fromShared (not $ null tn) tr b bix a
        if null tn
            then return a'
            else do a'' <- force a'
                    runB True tn b bix a''
    where (tr, tn, _, _) = runnable 32 s

runW :: (Scalar a)
     => Bool -> Bool -> Stage a -> Word32 -> Exp Word32
     -> Pull (Exp a) -> BProgram (Push (Exp a))
runW fromShared toShared s b bix a = if null tn
        then return a'
        else do a'' <- write a'
                runW True toShared tn b bix a''
    where a' = Push tl $ \wf ->
                    ForAll (Just tt) $ \tix -> do
                        let ix = (bix*(fromIntegral b)+tix)
                        runT fromShared toShared' tr b tt ix wf a
          (tr, tn, tl, tt) = runnable 1 s
          toShared' = toShared || (not $ null tn)

runT :: (Scalar a)
     => Bool -> Bool -> Stage a -> Word32 -> Word32 -> Exp Word32
     -> (Exp a -> Exp Word32 -> TProgram ())
     -> Pull (Exp a) -> TProgram ()
runT fromShared toShared [FMap f i o ob nn] b tt ix wf a =
      sequence_ [wf (fl !! (fromIntegral six))
                    ((divide toShared ix)*(fromIntegral (length o))+fromIntegral six)
                | six <- [0..(length o)-1]]
    where l = map (\ixf -> a!(divide fromShared $ ixf ix)) i
          fl = f l
          divide :: Bool -> Exp Word32 -> Exp Word32
          divide cond a = if cond
                        then simplifyMod b b tt a
                        else a
runT _ _ [] b tt ix wf a = return ()

--simplifying treating i as an integer modulo m
simplifyMod :: Word32 -> Word32 -> Word32 -> Exp Word32 -> Exp Word32
simplifyMod m bs tt = makeExp.sm.snd.sm --second time to get correct range after simplifications
  where sm :: Exp Word32 -> (Maybe (Word32,Word32),Exp Word32)
        sm (Literal a) = (Just (am,am),Literal am)
            where am = a`mod`m
        sm (BinOp Mul a b) = bop a b (*) (*)
        sm (BinOp Add a b) = bop a b (+) (+)
        sm (BinOp Sub a b) = bop a b (-) (-)
        sm (ThreadIdx X) | tt <= m = (Just (0,tt-1),ThreadIdx X)
        sm (ThreadIdx X) | bs <= m = (Just (0,bs-1),ThreadIdx X)
        sm a = (Nothing,a)
        bop :: Exp Word32 -> Exp Word32
            -> (Exp Word32 -> Exp Word32 -> Exp Word32)
            -> (Word32 -> Word32 -> Word32)
            -> (Maybe (Word32,Word32),Exp Word32)
        bop a b f fw = (r,av `f` bv)
            where (ab,av) = sm a
                  (bb,bv) = sm b
                  r = do
                    (al,ah) <- ab
                    (bl,bh) <- bb
                    guard $ al `fw` bl >= 0
                    guard $ ah `fw` bh < m
                    Just (al `fw` bl,ah `fw` bh)
        makeExp :: (Maybe (Word32,Word32),Exp Word32) -> Exp Word32
        makeExp (Just _,a) = a
        makeExp (Nothing,a) = a`mod`(Literal m)


quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

strace a = trace (show a) a

binOpStage :: (Scalar a) => (Exp a -> Exp a -> Exp a) -> Index -> Index -> FrontStage a ()
binOpStage f i1 i2 = SFMap (\[a,b] -> [a `f` b]) [i1,i2] [id]

reduce :: (Scalar a, Num (Exp a))  => FrontStage a ()
reduce = do
  l <- Len
  if l==1
    then Return ()
    else do binOpStage (+) id (+(fromIntegral l`div`2))
            reduce


testInput :: GlobPull (Exp Int)
testInput = namedGlobal "apa"
tr0 = quickPrint (run reduce 1024 2048) testInput

tr1 = mkStage 1024 1024 [id] (reduce :: FrontStage Int ())

{- TODO:
   Divide threads!!! sharedmem
     simplify mod expression
   TProgram
   runT composings
   lambda quadpair for additions
   algorithms:
        scan
        sort
        pack
        filter
 -}

