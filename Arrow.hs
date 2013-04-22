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

module Arrow (run,simpleRun,TraverseExp,(:->)
             ,aSync,aSyncInplace,aInplaceSync,liftG) where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian.Program hiding (Bind,Return,Sync)
import qualified Obsidian.Program as P
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Array
import Obsidian.Library
import Obsidian.Force
import Obsidian.Memory
import Obsidian.Globs
import Obsidian.Atomic
import Obsidian.Memory
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
import Inplace

import Prelude hiding (zipWith,sum,replicate,id,(.))
import qualified Prelude as P

data a :-> b where
  First  :: (a :-> b) -> ((a,d) :-> (b,d))
  Pure :: (a -> b) -> (a :-> b)
  Comb :: (a :-> b) -> (b :-> c) -> (a :-> c)
  --Pure :: (a -> b) -> (a :-> b)
  Sync :: (Array p, APushable p, MemoryOps b, TraverseExp b) -- => Forceable (Pull (Exp b))
       => (p Word32 b) :-> (Inplace Word32 b)
  InplaceSync :: (Array p, APushable p, MemoryOps b, TraverseExp b)
              => (Inplace Word32 b,p Word32 b) :-> ()
  Apply :: (b :-> c, b) :-> c
  Loop :: ((a,d) :-> (b,d)) -> (a :-> b)
  --For :: (MemoryOps a) => (a :-> (a,c,Bool)) -> a -> (a :-> c)
  --While :: (d :-> Bool) -> ((a,d) :-> (b,d)) -> (a :-> b)
  --While :: (a :-> Bool) -> (a :-> a) -> (a :-> a)

{-
instance Show (a :-> b) where
  show (Pure f) = "Pure f"
  show (Sync f g) = "Sync f (" ++ show g ++ ")"
  show (Apply f g) = "Apply f (" ++ show g ++ ")"
-}

instance Category (:->) where
  id = Pure id

  --(.) (Comb f g h) (Fst f') = Comb (fst.f) (g.f') h
  (.) o (Comb h g)    = Comb h (o . g)
  (.) o (Loop l)   = Loop (first o.l)
  (.) (Loop l) o   = Loop (l.first o)
  (.) a b = Comb b a

instance Arrow (:->) where
  arr = Pure
  --Comb (\a -> (f a,())) id (arr fst)
  --(***) (Pure f) (Pure g) = Pure $ \(x,y) -> (f x, g y)
  --(***) (Pure f) (Sync h g) = Sync t (r g)
  --  where t (a,d) = let (b,d') = h a
  --                  in (b,(d,d'))
  --        r = undefined
  --(***) (Pure f) (Pure g) = Pure $ \(x,y) -> (f x, g y)

  first = First

{-
  first (Pure f)   = Pure (mapFst f)
  first (Sync h g) = Sync (assoc.mapFst h) $ first g . arr unassoc
  first (Loop l)   = loop $ arr unassoc2 . first l . arr assoc2
  --first (Apply h g) = Apply h (r g)
  --  where t (a,d') = assoc (h a,d')
  --        r g = first g . arr unassoc
  first (Apply h g) = Apply (assoc.mapFst h) $ first g . arr unassoc
-}

mapFst f (a,b) = (f a, b)
assoc ((a,d),d') = (a,(d,d'))
unassoc (a,(d,d')) = ((a,d),d')
assoc2 ((a,d),d') = ((a,d'),d)
unassoc2 ((a,d'),d) = ((a,d),d')

instance ArrowApply (:->) where
  --app = Apply id id
  app = Apply -- (\a -> (a,())) (arr (\(a,()) -> a))
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


aSync :: (Array p, APushable p, MemoryOps a, TraverseExp a)
      => p Word32 a :-> Pull Word32 a
aSync = arr pullInplace . Sync -- (\a -> (a,())) (arr (\(a,()) -> pullInplace a))

aSyncInplace :: (Array p, APushable p, MemoryOps a, TraverseExp a)
      => p Word32 a :-> Inplace Word32 a
aSyncInplace = Sync

aInplaceSync :: (Array p, APushable p, MemoryOps a, TraverseExp a)
            => (Inplace Word32 a,p Word32 a) :-> ()
aInplaceSync = InplaceSync

liftG :: BProgram a -> GProgram a
liftG p = do
  ForAllBlocks 1 $ \bix ->
    p

simpleRun :: (a :-> b) -> a -> BProgram b
simpleRun (Pure f)     a = return $ f a
simpleRun (First f) (a,d) = do
  b <- simpleRun f a
  return (b,d)
simpleRun (Comb g h) a = do
  b <- simpleRun g a
  simpleRun h b
simpleRun Sync a = do
  forceInplace (apush a)
simpleRun InplaceSync (i,a) = do
  inplaceWrite i (apush a)
simpleRun Apply (h,a) = do
  simpleRun h a
--simpleRun (Loop l) a = do
--  n <- uniqueSM
--  SeqFor 10 $ \i -> do
--              (b,d) <- simpleRun l (a,Index (n,[]))
--              Assign n d
--              return b

type RunInfo b c = (Word32, Inplace Word32 b :-> c, APush Word32 b)
type TransformA = forall e. Transform e
type Transform e = (Word32 -> Exp e -> Exp e)

composeT t t' = \bsl -> t bsl . t' bsl

runTrans :: TransformA -> Word32 -> Word32 -> TProgram () -> TProgram ()
runTrans t bs l = traverseExp (t (min bs l))

run :: (MemoryOps b, TraverseExp b) => Word32 -> (a :-> Pull Word32 b)
    -> a -> GProgram ()
run bs g a = do
  (a',t) <- run' bs (const id) g aSync a
  forceG' $ pushG bs t (apush a')

run' :: Word32 -> TransformA -> (a :-> b) -> (b :-> c) -> a -> GProgram (b, TransformA)
run' bs t (Pure f)  after a = return (f a,const id)
run' bs t (First f) after (a,d) = do
  (b,t') <- run' bs t f (after.arr (\a -> (a,d))) a
  return ((b,d),t')
run' bs t (Comb g h) after a = do
  (b,t1) <- run' bs t g (after.h) a
  let t2 :: TransformA
      t2 = (composeT t t1)
  (c,t3) <- run' bs t2 h after b
  return (c,composeT t2 t3)
run' bs t Sync after a = do
  n <- uniqueSM
  let ri = (bs,after,apush a)
  if runBable ri
    then do
      ForAllBlocks (Literal (len a+bs-1 `div` bs)) $ \bid -> do
                --a'' <- force a'
                --return (a'',id)
                runB bid ri t
      --run' bs (composeT t t') g after a''
    else error "not implemented" {- do
      a' <- forceG (resize (fromIntegral (len (f a))) (push Grid (f a)))
      run' g a'
    -}
run' bs t InplaceSync after (i,a) = do
  let a'@(APush n wf) = apush a
      Inplace _ w r  = i
      bs' = fromIntegral bs
  ForAllBlocks (fromIntegral (n+bs-1 `div` bs)) $ \bid -> do
    ForAll (fromIntegral (min bs n)) $ \tid -> do
      wf w (bid*bs'+tid)
    P.Sync --keep some anlysis since we have already done this
  return ((),const id)


run' bs t Apply after (h,a) = do
  run' bs t h after a

runBable :: RunInfo b c -> Bool
runBable (bs,g,a) = True

runB :: (MemoryOps b, TraverseExp b)
     => Exp Word32
     -> RunInfo b c -> TransformA
     -> BProgram (Inplace Word32 b, TransformA)
runB bid ri@(bs,_,APush l ixf) t =
  if False --runWable ri
    then runW bid ri t
    else do
      (a'',ns) <- nameInplaceWrite a'
      P.Sync
      return (a'', divide ns f)
  where f = simplifyMod bs
        a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                      wid = f (min bs l) gid
                  in runTrans t bs l (ixf (flip wf) gid)

collectRun :: (TProgram () -> [d]) -> Exp Word32 -> (a :-> b) -> a -> (b, [(Word32,d)])
collectRun cf ix (Pure f)  a = (f a, [])
collectRun cf ix (First f) (a,d) =
  let (b,r) = collectRun cf ix f a
  in ((b,d),r)
collectRun cf ix (Comb g h) a = 
  let (a1,r1) = collectRun cf ix g a
      (a2,r2) = collectRun cf ix h a1
  in (a2, r1 ++ r2)
collectRun cf ix Sync a = 
  let a1@(APush n ixf) = apush a
      ns = createNames (valType a1) "noname"
      a2 = fakeForce a1 ns
  in (a2, addTup n (cf $ ixf (dummyWrite ns) ix))
  where addTup n ds = map (\d -> (n,d)) ds
        dummyWrite :: (MemoryOps a) => Names -> Exp Word32 -> a -> TProgram ()
        dummyWrite ns = (\i v -> assignArray ns v i)
collectRun cf ix InplaceSync (i,a) =
  let a1@(APush n ixf) = apush a
      (Inplace n' w r)    = i
  in ((), addTup n (cf $ ixf w ix))
  where addTup n ds = map (\d -> (n,d)) ds
collectRun cf ix Apply (h,a) = collectRun cf ix h a

runWable :: (MemoryOps b, TraverseExp b) => RunInfo b c -> Bool
runWable ri@(bs,g,a) = runAable (isDivable 32 bs (len a)) ri

runW :: (MemoryOps b, TraverseExp b)
     => Exp Word32
     -> RunInfo b c -> TransformA
     -> BProgram (Inplace Word32 b, TransformA)
runW bid ri@(bs,_,APush l ixf) t =
  if runTable ri
    then ForAll (fromIntegral bs) $ \tid -> 
          runT (bid*(fromIntegral bs)+tid) ri t
    else do
      (a''',ns) <- nameInplaceWrite a''
      return (a''', divide ns f)
  where f = simplifyMod bs
        a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                  in runTrans t bs l (ixf (flip wf) gid)
        a'' = ixMap (f (min bs l)) a'

runTable :: (MemoryOps b, TraverseExp b) => RunInfo b c -> Bool
runTable ri@(bs,g,a) = runAable (\gid (n,a) -> (gid==a)) ri

valType :: a b m -> m
valType = (undefined :: m)

runT :: (MemoryOps b, TraverseExp b)
     => Exp Word32
     -> RunInfo b c -> TransformA
     -> TProgram (Inplace Word32 b, TransformA)
runT gid ri@(bs,_,a@(APush l ixf)) t = do
  let v = valType a
  n <- names v
  allocateScalar n v
  let p = ixf (\_ v -> assignScalar n v) gid
  runTrans t bs (len a) p
  return (inplaceVariable (len a) n, const id)  --(Pull (len a) $ \_ -> readFrom n, const id)

divide :: Names -> (Word32 -> Exp Word32 -> Exp Word32)
       -> Transform b
divide n f bsl = traverseOnIndice n (f bsl)

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

runAable :: (MemoryOps b, TraverseExp b)
         => (Exp Word32 -> (Word32,Exp Word32) -> Bool)
         -> RunInfo b c -> Bool
runAable f ri@(bs,g,a) = 
  let ns = createNames (valType a) "target"
      a' = fakeForce a ns
      gid = (BlockIdx X*(fromIntegral bs) +(ThreadIdx X))
      accesses = snd $ collectRun (snd.collectProg (getIndice ns)) gid g a'
  in strace $ if accesses /= []
      then all (gid `f`) accesses
      else error ("No uses of this array: " ++ show accesses)

fakeForce :: (Array a1, MemoryOps e)
          => a1 Word32 e -> Names -> Inplace Word32 e
fakeForce a ns = inplace (len a) ns

pushG :: (TraverseExp a, ASize s) => Word32 -> TransformA
      -> APush Word32 a -> Push Grid s a
pushG bs t (APush l ixf) = Push (fromIntegral l) $ \wf ->
  ForAllBlocks (fromIntegral $ (l+bs-1) `div` bs) $ \bid ->
    ForAll (fromIntegral (min l bs)) $ \tid ->
      let gid = bid*(fromIntegral bs)+tid
      in runTrans t bs l (ixf (flip wf) gid)

strace a = trace (show a) a

{-

Todo:
Strategies:
  accesses
  threadids
  transpose
Instead of replacing accesses, do it in Pull
  where do we get size?
MPI

-}
