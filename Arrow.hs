{-# LANGUAGE ScopedTypeVariables,
             GADTs,
             RankNTypes,
             ExistentialQuantification,
             MultiParamTypeClasses,
             FlexibleInstances,
             TypeFamilies,
             TypeOperators,
             Arrows,
             ImpredicativeTypes,
             FlexibleContexts #-}

module Stages where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian.Program hiding (Bind,Return,Sync)
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Array
import Obsidian.Library
import Obsidian.Force
import Obsidian.Memory
import Obsidian.Globs
import Obsidian.Atomic
import Debug.Trace

import Data.Word
import Data.Int
import Data.Bits
import Data.Maybe

import qualified Data.Vector.Storable as V

--import Control.Monad.State
import Control.Category
import Control.Arrow
import Control.Monad
--import Control.Monad.Loop
import Control.Arrow.ApplyUtils

import ExpAnalysis

import Prelude hiding (zipWith,sum,replicate,id,(.))
import qualified Prelude as P

type G b c = (Pull Word32 (Exp b) :-> c)

data a :-> b where
  Pure :: (a -> b) -> (a :-> b)
  Sync :: (Scalar b) -- => Forceable (Pull (Exp b))
          => (a -> (Pull Word32 (Exp b),d))
          -> ((Pull Word32 (Exp b),d) :-> c)
          -> (a :-> c)
  Loop :: ((a,d) :-> (b,d)) -> (a :-> b)
  Apply :: (a -> ((b :-> c, b),d)) -> ((c,d) :-> e) -> (a :-> e)
  --Comp :: (a -> b) (b :-> c) 

instance Show (a :-> b) where
  show (Pure f) = "Pure f"
  show (Sync f g) = "Sync f (" ++ show g ++ ")"

instance Category (:->) where
  id = Pure id

  (.) (Pure f) (Pure g)    = Pure (f . g)
  (.) (Sync h g) (Pure f)  = Sync (h . f) g
  --(.) (Pure f) (Sync h g) = Sync h (Pure f . g)
  (.) o (Sync h g) = Sync h (o . g)
  (.) o (Loop l)   = Loop (first o.l)
  (.) (Loop l) o   = Loop (l.first o)
  (.) (Apply h g) (Pure f) = Apply (h . f) g
  (.) o (Apply h g) = Apply h (o . g)
  --(.) a b = error $ show a " " ++ show b

instance Arrow (:->) where
  arr = Pure
  --(***) (Pure f) (Pure g) = Pure $ \(x,y) -> (f x, g y)
  --(***) (Pure f) (Sync h g) = Sync t (r g)
  --  where t (a,d) = let (b,d') = h a
  --                  in (b,(d,d'))
  --        r = undefined
  --(***) (Pure f) (Pure g) = Pure $ \(x,y) -> (f x, g y)

  first (Pure f)   = Pure (mapFst f)
  first (Sync h g) = Sync (assoc.mapFst h) $ first g . arr unassoc
  first (Loop l)   = loop $ arr unassoc2 . first l . arr assoc2
  --first (Apply h g) = Apply h (r g)
  --  where t (a,d') = assoc (h a,d')
  --        r g = first g . arr unassoc
  first (Apply h g) = Apply (assoc.mapFst h) $ first g . arr unassoc

mapFst f (a,b) = (f a, b)
assoc ((a,d),d') = (a,(d,d'))
unassoc (a,(d,d')) = ((a,d),d')
assoc2 ((a,d),d') = ((a,d'),d)
unassoc2 ((a,d'),d) = ((a,d),d')

instance ArrowApply (:->) where
  --app = Apply id id
  app = Apply (\a -> (a,())) (Pure (\(a,()) -> a))
{-
  app = Pure $ (uncurry app')
    where app' :: (a :-> b) -> a -> b
          app' arr a =
            case arr of
              Pure f   -> f a
              Sync h g -> app' g (h a)
-}

{-
instance ArrowChoice (:->) where
  left = undefined
instance ArrowChoice (:->) where
  left f  = f +++ id
  right f = id +++ f
  f +++ g = (f >>> arr Left) ||| (g >>> arr Right)
  (Pure f) ||| (Pure g) = arr (either f g)
-}

instance ArrowLoop (:->) where
  loop = Loop


-- More or less means that only "Exps" are ever allowed..
-- Try to generalise. Force is to blame for this.. 
aSync :: (Scalar a) => Pull Word32 (Exp a) :-> Pull Word32 (Exp a)
aSync = Sync (\a -> (a,())) (Pure (\(a,()) -> a))

liftG :: BProgram a -> GProgram a
liftG p = do
  ForAllBlocks 1 $ \bix ->
    p

simpleRun :: (a :-> b) -> a -> BProgram b
simpleRun (Pure f)   a = do
  return (f a)
simpleRun (Sync f g) a = do
  let (a',d) = f a
  a'' <- force a'
  simpleRun g (a'',d)
simpleRun (Apply f g) a = do
  let ((h,b),d) = f a
  a' <- simpleRun h b
  simpleRun g (a',d)
--simpleRun (Loop l) a = do
--  n <- uniqueSM
--  SeqFor 10 $ \i -> do
--              (b,d) <- simpleRun l (a,Index (n,[]))
--              Assign n d
--              return b

type RunInfo b c d = (Word32, ((Pull Word32 (Exp b),d) :-> c), Pull Word32 (Exp b), d)
type TransformA = forall e. Transform e
type Transform e = (Scalar e) => (Word32 -> Exp e -> Exp e)



run :: (Scalar b) => Word32 -> (a :-> Pull Word32 (Exp b))
    -> a -> GProgram ()
run bs g a = do
  (a',t) <- run' bs (const id) g a
  forceG $ pushG bs t a'

pushG :: (Scalar a) => Word32 -> Transform a
      -> Pull Word32 (Exp a) -> Push Grid (Exp Word32) (Exp a)
pushG bs t (Pull l ixf) = Push (fromIntegral l) $ \wf ->
  ForAllBlocks (fromIntegral $ (l+bs-1) `div` bs) $ \bid ->
    ForAll (fromIntegral (min l bs)) $ \tid ->
      let gid = bid*(fromIntegral bs)+tid
      in wf (t (min l bs) (ixf gid)) gid

run' :: Word32 -> TransformA -> (a :-> b) -> a -> GProgram (b, TransformA)
run' bs t (Pure f)   a = do
  --forceG (resize (fromIntegral (len (f a))) (push Grid (f a)))
  return (f a,t)
run' bs t (Sync f g) a = do
  n <- uniqueSM
  let (a',d) = f a
      ri = (bs,g,a',d)
  if runBable ri
    then do
      (a'',t') <- ForAllBlocks (Literal (len a'+bs-1 `div` bs)) $ \bid -> do
                --a'' <- force a'
                --return (a'',id)
                runB bid ri t
      run' bs (composeT t t') g (a'',d)
    else error "not implemented" {- do
      a' <- forceG (resize (fromIntegral (len (f a))) (push Grid (f a)))
      run' g a'
    -}
run' bs t (Apply f g) a = do
  let ((h,b),d) = f a
  (a',t') <- run' bs t h b
  run' bs (composeT t t') g (a',d)


composeT t t' = \bsl -> t bsl . t' bsl

runBable :: RunInfo b c d -> Bool
runBable (bs,g,a,d) = True

fakeForce :: (Scalar a, Array a1, ASize s)
          => a1 s e -> Name -> Pull s (Exp a)
fakeForce a n = namedPull n (len a)

runB :: (Scalar b)
     => Exp Word32
     -> RunInfo b c d -> Transform b
     -> BProgram (Pull Word32 (Exp b), TransformA)
runB bid ri@(bs,_,Pull l ixf,_) t =
  if runWable ri
    then runW bid ri t
    else do
      a'' <- force a'
      return (a'', divide (getName a'') f)
  where f = simplifyMod bs
        a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                      wid = f (min bs l) gid
                  in wf (t (min bs l) (ixf gid)) wid

getName :: Pull Word32 (Exp a) -> Name
getName (Pull n ixf) = let Index (n,_) = ixf (Literal 0)
                       in n

addTup n ds = map (\d -> (n,d)) ds

collectRun :: (forall c. Exp c -> [d]) -> Exp Word32 -> (a :-> b) -> a -> (b, [(Word32,d)])
collectRun cf ix (Pure f)   a = (f a, []) -- case f a of Pull n ixf -> addTup n (cf $ ixf ix)
collectRun cf ix (Sync f g) a =
  let (a'@(Pull n ixf),d) = f a
      a'' = fakeForce a' "noname"
      (a''',r) = collectRun cf ix g (a'',d)
  in (a''', addTup n (cf $ ixf ix) ++ r)
collectRun cf ix (Apply f g) a =
  let ((h,b),d) = f a
      (a',r)    = collectRun cf ix h b
      (a'',r2)  = collectRun cf ix g (a',d) 
  in (a'', r ++ r2)
  {-
simpleRun (Apply f g) a = do
  let ((h,b),d) = f a
  a' <- simpleRun h b
  simpleRun g (a',d)
  -}

isDivable :: Word32 -> Word32 -> Word32 -> Exp Word32 -> (Word32, Exp Word32) -> Bool
isDivable m bs ngid gid (na,a) =
  let a' = (simplifyDiv m bs na a)
      b' = (simplifyDiv m bs ngid gid) 
  in trace ((show m) ++ " \\ " ++
            (show a) ++ " -> " ++
            (show a') ++ " == " ++
            (show gid) ++ " -> " ++
            (show b') ++ " = " ++
            (show (a' == b')) ++ "\n"
           )
           $ a' == b'

runAable :: (Scalar b) => (Exp Word32 -> (Word32,Exp Word32) -> Bool) -> RunInfo b c d -> Bool
runAable f ri@(bs,g,a,d) =
  let n = "target"
      gid = (BlockIdx X*(fromIntegral bs) +(ThreadIdx X))
      a' = fakeForce a n
      accesses = snd $ collectRun (collectExp (getIndice n) (++)) gid g (a',d)
  in strace $ accesses /= [] && all (gid `f`) accesses

runWable :: (Scalar b) => RunInfo b c d -> Bool
runWable ri@(bs,g,a,d) = runAable (isDivable 32 bs (len a)) ri

runW :: (Scalar b)
     => Exp Word32
     -> RunInfo b c d -> Transform b
     -> BProgram (Pull Word32 (Exp b), TransformA)
runW bid ri@(bs,_,Pull l ixf,_) t =
  if runTable ri
    then ForAll (fromIntegral bs) $ \tid -> 
          runT (bid*(fromIntegral bs)+tid) ri t
    else do
      a'' <- write a'
      return (a'', divide (getName a'') f)
  where f = simplifyMod bs
        a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                      wid = f (min bs l) gid
                  in wf (t (min bs l) (ixf gid)) wid

runTable :: (Scalar b) => RunInfo b c d -> Bool
runTable ri@(bs,g,a,d) = runAable (\gid (n,a) -> (gid==a)) ri

runT :: (Scalar b)
     => Exp Word32
     -> RunInfo b c d -> Transform b
     -> TProgram (Pull Word32 (Exp b), TransformA)
runT gid ri@(bs,_,a,_) t = do
  let v = t (min bs (len a)) $ a ! gid
  n <- uniqueSM
  Assign n [] v
  return (Pull (len a) $ \_ -> variable n, const id)

divide :: (Scalar b)
       => Name -> (Word32 -> Exp Word32 -> Exp Word32)
       -> Word32 -> Exp b -> Exp b
divide n f bsl = traverseExp (traverseOnIndice n (f bsl))


testInput :: Pull Word32 (Exp Int)
testInput = namedGlobal "apa" 2048

testInput' :: Pull (Exp Word32) (Exp Int)
testInput' = namedGlobal "apa" 2048

testInputS :: Pull Word32 (Exp Int)
testInputS = namedGlobal "apa" 512

testInputW :: Pull Word32 (Exp Word32)
testInputW = namedGlobal "apa" 512

liftE a = resize (fromIntegral (len a)) a

reduce0 :: (Scalar a, Num (Exp a)) => Word32 -> (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce0 1 = id
reduce0 n = (uncurry (zipWith (+)) <<< halve)
       ^>> aSync
       >>> reduce0 (n`div`2)
tr0 = quickPrint t testInput
  where s a = liftG $ simpleRun (reduce0 (len a)) a
        t a = run 1024 (reduce0 (len a)) a 

reduce1 :: (Scalar a, Num (Exp a)) => Word32 -> (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce1 n = (uncurry (zipWith (+)) <<< halve)
       ^>> if n == 2
        then id
        else aSync
         >>> reduce1 (n`div`2)
tr1 = quickPrint t testInput
  where t a = run 1024 (reduce1 (len a)) a 

reduce2 :: (Scalar a, Num (Exp a)) => (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce2 = proc a -> do
      rec a' <- Pure (halve >>> uncurry (zipWith (+))) -< a
          b <- aSync -< a'
          a <- id -< if len a == 1 then b else b
      returnA -< a
tr2 = quickPrint s testInput
  where s a = liftG $ simpleRun reduce2 a
        t a = run 1024 reduce2 a

appl :: ArrowApply a => a b c -> a b c
appl a = proc b -> do app -< (a,b)


reduce3 :: (Scalar a, Num (Exp a)) => (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce3 = proc a -> do
      let b = uncurry (zipWith (+)) $ halve a
      app -< (if len b == 1 then id else reduce3 <<< aSync,b)
tr3 = quickPrint t testInput
  where s a = liftG $ simpleRun reduce3 a
        t a = run 1024 reduce3 a

type a :~> b = a -> ArrowAsMonad (:->) b

reduce4 :: (Scalar a, Num (Exp a)) => Pull Word32 (Exp a) :~> (Pull Word32 (Exp a))
reduce4 a = do
  let b = uncurry (zipWith (+)) $ halve a
  if len b == 1
    then return b
    else (unmonadicA aSync >=> reduce4) b
tr4 = quickPrint t testInput
  where s a = liftG $ simpleRun (monadicA reduce4) a
        t a = run 1024 (monadicA reduce4) a

mine :: (Scalar a, Ord (Exp a)) => Exp a -> Exp a -> Exp a
mine = BinOp Min
maxe :: (Scalar a, Ord (Exp a)) => Exp a -> Exp a -> Exp a
maxe = BinOp Max

bitonicMerge0 :: (Scalar a, Ord (Exp a)) => ((Pull Word32 (Exp a),Word32) :-> Pull Word32 (Exp a))
bitonicMerge0 = proc (a,s) -> do
  let s' = fromIntegral s
      b = Pull (len a) $ \i -> If (i .&. s' ==* 0)
                                  (mine (a!i) (a!(i `xor` s')))
                                  (maxe (a!i) (a!(i `xor` s')))
  app -< (if s == 1 then arr fst else bitonicMerge0 <<< first aSync,(b,s`div`2))
bitonic0 :: (Scalar a, Ord (Exp a)) => Pull Word32 (Exp a) :-> Pull Word32 (Exp a)
bitonic0 = proc a -> do
  bitonicMerge0 -< (a,len a)
tb0 = quickPrint t testInputS
  where s a = liftG $ simpleRun bitonicMerge0 (a,len a)
        t a = run 1024 bitonicMerge0 (a,len a)


mSync :: (Scalar a) => Pull Word32 (Exp a) :~> Pull Word32 (Exp a)
mSync = unmonadicA aSync

type PullC a = Pull Word32 (Exp a)

listRank0 :: (Exp (Word32) -> Exp Bool) -> Pull Word32 (Exp Word32) :~> Pull Word32 (Exp Word32)
listRank0 isNull nexti = do
  let ranki :: Pull Word32 (Exp Word32)
      ranki = fmap (\v -> If (isNull v) 0 1) nexti
      s = len nexti
  (nextf,rankf) <- f s (ranki,nexti)
  --(nextf,rankf) <- concatM (replicate (getNext2Power s) f) (ranki,nexti)
  return rankf
    where f :: Word32 -> (PullC Word32, PullC Word32) :~> (PullC Word32, PullC Word32)
          f n (rank,next) = do
            let (rankn,nextn) = unzipp $ Pull (len nexti) $ \k ->
                    let nk = next!k
                    in ifp (isNull nk)
                        (rank!k,next!k)
                        ((rank!k) + (rank!nk), next!nk)
            ranks <- mSync rankn
            nexts <- mSync nextn
            if n == 0
              then return (ranks,nexts)
              else f (n`div`2) (ranks,nexts)
tl0 = quickPrint t testInputW
  where s a = liftG $ simpleRun (monadicA $ listRank0 p) a
        t a = run 1024 (monadicA $ listRank0 p) a
        p v = v ==* 0

concatM :: Monad m => [a -> m a] -> a -> m a
concatM fs = foldr (>=>) return fs

ifp :: (Scalar a, Scalar b) => (Exp Bool) -> (Exp a, Exp b) -> (Exp a, Exp b) -> (Exp a, Exp b)
ifp p (a1,a2) (b1,b2) = (If p a1 b1, If p a2 b2)

{-

Todo:
Strategies:
  accesses
  threadids
  transpose
Instead of replacing accesses, do it in Pull
MPI

-}
