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
  FMap  :: (Scalar a) => ([Exp a] -> TProgram [Exp a]) -> [Index] -> [Index] -> [Index] -> Word32 -> BackStage a

type Stage a = [BackStage a]

data FrontStage a b where
  SFMap  :: (Scalar a) => ([Exp a] -> TProgram [Exp a]) -> [Index] -> [Index] -> FrontStage a ()
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
  show (FMap f i o ob nn) = "FMap f " ++ show (length i) ++ " " ++ show (length o) ++  " " ++ show (length ob) ++ " " ++ show nn

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
        getConstant (Literal c) = Just c
        getConstant nc          = error $ "Cannot get constant for: " ++ (show nc)

runnable :: (Scalar a)
        => Word32 -> Stage a
        -> (Stage a, Stage a, Word32, Word32)
runnable divisions as = runone as
  where runnable' :: (Scalar a)
                  => Stage a
                  -> (Stage a, Stage a, Word32, Word32)
        runnable' ao@(a@(FMap f i o ob nn) : as) =
            if null ob
               || (nn`div`(fromIntegral (length ob))) <= divisions
               || accessA divisions ob nn i
                then runone ao
                else ([], ao, nn, 0)
        runone :: (Scalar a)
               => Stage a
               -> (Stage a, Stage a, Word32, Word32)
        runone (a:as) = 
            if null as || (divisions == 1 && tt1 /= tt2) --special case
                then ([tr1],     as,  tl1, tt1)
                else (tr1 : tr2, tn2, tl2, tt1)
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
runT fromShared toShared [FMap f i o ob nn] b tt ix wf a = do
      fl <- f l
      sequence_ [wf (fl !! (fromIntegral six))
                    ((divide toShared ix)*(fromIntegral (length o))+fromIntegral six)
                | six <- [0..(length o)-1]]
    where l = map (\ixf -> a!(divide fromShared $ ixf ix)) i
          divide :: Bool -> Exp Word32 -> Exp Word32
          divide cond a = if cond
                        then simplifyMod b (b`min`tt) a
                        else a
runT _ _ [] b tt ix wf a = return ()

--simplifying treating i as an integer modulo m
simplifyMod :: Word32 -> Word32 -> Exp Word32 -> Exp Word32
simplifyMod m bs = makeExp.sm.snd.sm --second time to get correct range after simplifications
  where sm :: Exp Word32 -> (Maybe (Word32,Word32),Exp Word32)
        sm (Literal a) = (Just (am,am),Literal am)
            where am = a`mod`m
        sm (BinOp Mul a b) = bop a b (*) (\al ah bl bh -> Just (al*bl,ah*bh))
        sm (BinOp Add a b) = bop a b (+) (\al ah bl bh -> Just (al+bl,ah+bh))
        sm (BinOp Sub a b) = bop a b (-) (\al ah bl bh -> Just (al-bh,ah-bl))
        sm (BinOp Div a b) = bop a b div (\al ah bl bh -> Just (al`div`bh,ah`div`bl))
        sm a@(BinOp Mod _ (Literal b)) = (Just (0,b-1),a)
        sm (ThreadIdx X) = (Just (0,bs-1),ThreadIdx X)
        sm a = (Nothing,a)
        bop :: Exp Word32 -> Exp Word32
            -> (Exp Word32 -> Exp Word32 -> Exp Word32)
            -> (Word32 -> Word32 -> Word32 -> Word32 -> Maybe (Word32,Word32))
            -> (Maybe (Word32,Word32),Exp Word32)
        bop a b f fw = (r,av `f` bv)
            where (ab,av) = sm a
                  (bb,bv) = sm b
                  r = do
                    (al,ah) <- ab
                    (bl,bh) <- bb
                    --guard $ al `fw` bl >= 0
                    --guard $ ah `fw` bh < m
                    fw al ah bl bh
        makeExp :: (Maybe (Word32,Word32),Exp Word32) -> Exp Word32
        makeExp (Just (l,h),a) | l>=0 && h<m = a
        makeExp (Nothing,a) = error $ "Not modable by m" ++ (show a) --a`mod`(Literal m)


quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

strace a = trace (show a) a

binOpStage :: (Scalar a) => (Exp a -> Exp a -> Exp a) -> Index -> Index -> FrontStage a ()
binOpStage f i1 i2 = SFMap (\[a,b] -> return [a `f` b]) [i1,i2] [id]

collectExp :: (Exp a -> b) -> (b -> b -> b) -> Exp a -> b
collectExp f g c@(BinOp Mul a b) = (collectExp f g a) `g` (collectExp f g b) `g` f c
collectExp f g c@(BinOp Add a b) = (collectExp f g a) `g` (collectExp f g b) `g` f c
collectExp f g c@(BinOp Sub a b) = (collectExp f g a) `g` (collectExp f g b) `g` f c
collectExp f g a = f a


traverseBin :: (Num (Exp a)) => (b -> Exp a -> (Exp a,b)) -> b -> Exp a -> Exp a 
            -> (Exp a -> Exp a -> Exp a) -> (Exp a,b)
traverseBin f d a b op = (lv `op` rv, rd)
    where (lv,ld) = traverseExp f d a
          (rv,rd) = traverseExp f ld b

traverseExp :: (Num (Exp a)) => (b -> Exp a -> (Exp a,b)) -> b -> Exp a -> (Exp a,b)
traverseExp f d (BinOp Mul a b) = traverseBin f d a b (*)
traverseExp f d (BinOp Add a b) = traverseBin f d a b (+)
traverseExp f d (BinOp Sub a b) = traverseBin f d a b (-)
traverseExp f d a = f d a



fakeProg :: (Scalar a, Num (Exp a)) => (Exp Word32 -> Pull (Exp a) -> Exp a) -> FrontStage a ()
fakeProg f = do
  l <- Len
  let e = f (Index ("Index",[])) (Pull l (\i -> Index ("Read", [i])))
      i = extractIndices e
      rf = \x -> return [replace "Read" e x]
      i' = [\ix -> replace "Index" ixf [ix] | ixf <- i]
  SFMap rf i' [id]
  where extractIndices :: Exp a -> [Exp Word32]
        extractIndices = collectExp f (++)
            where f a@(Index ("Read",[i])) = [i]
                  f a                      = []
        replace :: (Scalar a, Num (Exp a)) => String -> Exp a -> [Exp a] -> Exp a
        replace n a x = let (r,[]) = replaceValues n x a in r
        replaceValues :: (Scalar a, Num (Exp a)) =>  String -> [Exp a] -> Exp a -> (Exp a, [Exp a])
        replaceValues n = traverseExp f 
            where f (x:xs) (Index (n',_ ))| n==n' = (x,xs)
                  f xs     x                      = (x,xs)
        replaceAllValues n v = traverseExp f ()
            where f () (Index (n',_ ))| n==n' = (v,())
                  f () x                    = (x,())


testInput :: GlobPull (Exp Int)
testInput = namedGlobal "apa"

reduce0 :: (Scalar a, Num (Exp a))  => FrontStage a ()
reduce0 = do
  l <- Len
  if l==1
    then Return ()
    else do binOpStage (+) id (+(fromIntegral l)`div`2)
            reduce0
tr0 = quickPrint (run reduce0 1024 2048) testInput
--tr0' = mkStage 1024 1024 [id] (reduce0 :: FrontStage Int ())

reduce1 :: (Scalar a, Num (Exp a))  => FrontStage a ()
reduce1 = do
  l <- Len
  if l==1
    then Return ()
    else do fakeProg $ \ix a -> (a!ix) + (a!(ix + (fromIntegral (len a)`div`2)))
            reduce1
tr1 = quickPrint (run reduce1 1024 2048) testInput

scan0 :: (Scalar a, Num (Exp a))  => FrontStage a ()
scan0 = do
    buildup 1
    where buildup s = do
            l <- Len
            if s >= l 
                then fakeProg $ \ix a -> if ix==0 then 0 else a!ix
                else do
                    --SFMap (\(a:as) -> return (a+as!!s:as)) [(+d) | d <- [s*2-1..0]] [(+d) | d <- [s*2-1..0]]
                    --buildup (s*2)
                    --SFMap (\(a:as) -> return (a+as!!s:as)) [(+d) | d <- [s*2-1..0]] [(+d) | d <- [s*2-1..0]]
                    
                    SFMap (\[a,b] -> return [a + b]) [(*2),(+1).(*2)] [id]
                    --fakeProg $ \ix a -> (a!(ix*2)) + (a!(ix*2+1))
                    --buildup (s*2)
                    fakeProg $ \ix a -> If (ix==*0) 0 $ If (ix`mod`2==*0) (a!(ix`div`2)) (a!(ix`div`2-1))
ts0 = quickPrint (run scan0 1024 1024) testInput

bitonic0 :: (Scalar a, Ord a)  => FrontStage a ()
bitonic0 = do
    --SFMap (\[a,b,c,d] -> return [a`mine`b,a`maxe`b,c`maxe`d,c`mine`d]) [id,(+1),(+2),(+3)] [id,(+1),(+2),(+3)]
    l <- Len
    br (l`div`2)
    where br d =
            if d==0
                then return ()
                else do
                    SFMap (\[a,b] -> return [a`mine`b,a`maxe`b]) [ixf,(+de).ixf] [ixf,(+de).ixf]
                    br (d`div`2)
                        where ixf i = i`mod`de+(i`div`de)*2*de
                              de = fromIntegral d

mine :: (Scalar a, Ord a) => Exp a -> Exp a -> Exp a
mine = BinOp Min
maxe :: (Scalar a, Ord a) => Exp a -> Exp a -> Exp a
maxe = BinOp Max

tb0 = quickPrint (run bitonic0 1024 1024) testInput

{- TODO:
   TProgram with assignments
   runT composings
   lambda quadpair for additions
   return false
   algorithms:
        scan
        sort
        pack
        filter
 -}

