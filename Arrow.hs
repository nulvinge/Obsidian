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

module Arrow where

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

import Prelude hiding (zipWith,sum,replicate,id,(.))
import qualified Prelude as P

type G b c = (Pull Word32 (Exp b) :-> c)

data a :-> b where
  Pure :: (a -> b) -> (a :-> b)
  Sync :: (TraverseExp b) -- => Forceable (Pull (Exp b))
          => (a -> (Pull Word32 b,d))
          -> ((Pull Word32 b,d) :-> c)
          -> (a :-> c)
  Loop :: ((a,d) :-> (b,d)) -> (a :-> b)
  Apply :: (a -> ((b :-> c, b),d)) -> ((c,d) :-> e) -> (a :-> e)
  --While :: (d :-> Bool) -> ((a,d) :-> (b,d)) -> (a :-> b)
  --Comp :: (a -> b) (b :-> c) 

instance Show (a :-> b) where
  show (Pure f) = "Pure f"
  show (Sync f g) = "Sync f (" ++ show g ++ ")"
  show (Apply f g) = "Apply f (" ++ show g ++ ")"

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
aSync :: (TraverseExp a) => Pull Word32 a :-> Pull Word32 a
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

type RunInfo b c d = (Word32, ((Pull Word32 b,d) :-> c), Pull Word32 b, d)
type TransformA = forall e. Transform e
type Transform e = (Word32 -> Exp e -> Exp e)

composeT t t' = \bsl -> t bsl . t' bsl

runTrans :: (TraverseExp a)
         => TransformA -> Word32 -> Word32 -> a -> a
runTrans t bs l a = traverseExp (t (min bs l)) a

run :: (TraverseExp b) => Word32 -> (a :-> Pull Word32 b)
    -> a -> GProgram ()
run bs g a = do
  (a',t) <- run' bs (const id) g id a
  forceG' $ pushG bs t a'

run' :: Word32 -> TransformA -> (a :-> b) -> (b :-> c) -> a -> GProgram (b, TransformA)
run' bs t (Pure f)   after a = do
  --forceG (resize (fromIntegral (len (f a))) (push Grid (f a)))
  return (f a,t)
run' bs t (Sync f g) after a = do
  n <- uniqueSM
  let (a',d) = f a
      --ri :: RunInfo b c d
      ri = (bs,after.g,a',d)
  if runBable ri
    then do
      (a'',t') <- ForAllBlocks (Literal (len a'+bs-1 `div` bs)) $ \bid -> do
                --a'' <- force a'
                --return (a'',id)
                runB bid ri t
      run' bs (composeT t t') g after (a'',d)
    else error "not implemented" {- do
      a' <- forceG (resize (fromIntegral (len (f a))) (push Grid (f a)))
      run' g a'
    -}
run' bs t (Apply f g) after a = do
  let ((h,b),d) = f a
  (a',t') <- run' bs t h (after.g.arr (\x -> (x,d))) b
  run' bs (composeT t t') g after (a',d)


runBable :: RunInfo b c d -> Bool
runBable (bs,g,a,d) = True

runB :: (TraverseExp b)
     => Exp Word32
     -> RunInfo b c d -> TransformA
     -> BProgram (Pull Word32 b, TransformA)
runB bid ri@(bs,_,Pull l ixf,_) t =
  if runWable ri
    then runW bid ri t
    else do
      (a'',ns) <- nameWrite a'
      P.Sync
      return (a'', divide ns f)
  where f = simplifyMod bs
        a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                      wid = f (min bs l) gid
                  in wf (runTrans t bs l (ixf gid)) wid

collectRun :: (forall c. TraverseExp c => c -> [d]) -> Exp Word32 -> (a :-> b) -> a -> (b, [(Word32,d)])
collectRun cf ix (Pure f)   a = (f a, []) -- case f a of Pull n ixf -> addTup n (cf $ ixf ix)
collectRun cf ix (Sync f g) a = 
  let (a'@(Pull n ixf),d) = f a
      ns = createNames (a'!0) "noname"
      a'' = fakeForce a' ns
      (a''',r) = collectRun cf ix g (a'',d)
  in (a''', addTup n (cf $ ixf ix) ++ r)
  where addTup n ds = map (\d -> (n,d)) ds
collectRun cf ix (Apply f g) a =
  let ((h,b),d) = f a
      (a',r)    = collectRun cf ix h b
      (a'',r2)  = collectRun cf ix g (a',d) 
  in (a'', r ++ r2)


runWable :: (TraverseExp b) => RunInfo b c d -> Bool
runWable ri@(bs,g,a,d) = runAable (isDivable 32 bs (len a)) ri

runW :: (TraverseExp b)
     => Exp Word32
     -> RunInfo b c d -> TransformA
     -> BProgram (Pull Word32 b, TransformA)
runW bid ri@(bs,_,Pull l ixf,_) t =
  if runTable ri
    then ForAll (fromIntegral bs) $ \tid -> 
          runT (bid*(fromIntegral bs)+tid) ri t
    else do
      (a'',ns) <- nameWrite a'
      return (a'', divide ns f)
  where f = simplifyMod bs
        a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                      wid = f (min bs l) gid
                  in wf (runTrans t bs l (ixf gid)) wid

runTable :: (TraverseExp b) => RunInfo b c d -> Bool
runTable ri@(bs,g,a,d) = runAable (\gid (n,a) -> (gid==a)) ri

runT :: (TraverseExp b)
     => Exp Word32
     -> RunInfo b c d -> TransformA
     -> TProgram (Pull Word32 b, TransformA)
runT gid ri@(bs,_,a,_) t = do
  let v = traverseExp (t (min bs (len a))) $ a ! gid
  n <- names v
  allocateScalar n v
  assignScalar n v
  return (Pull (len a) $ \_ -> readFrom n, const id)

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

runAable :: (TraverseExp b) => (Exp Word32 -> (Word32,Exp Word32) -> Bool) -> RunInfo b c d -> Bool
runAable f ri@(bs,g,a,d) =
  let ns = createNames (a!0) "target"
      a' = fakeForce a ns
      gid = (BlockIdx X*(fromIntegral bs) +(ThreadIdx X))
      accesses = snd $ collectRun (collectExp (getIndice ns) (++)) gid g (a',d)
  in strace $ (strace accesses) /= [] && all (gid `f`) accesses

fakeForce :: (Array a1, MemoryOps e)
          => a1 Word32 e -> Names -> Pull Word32 e
fakeForce a n = pullFrom n (len a)

nameWrite :: forall a p. (Array p, Pushable p, MemoryOps a)
          => p Word32 a -> BProgram (Pull Word32 a, Names)
nameWrite arr = do
  snames <- names (trace "nn" (undefined :: a) :: (MemoryOps a) => a)
  let n = len arr
  allocateArray snames (trace "nw" (undefined :: a)) n
  let (Push m p) = push Block arr
  p (assignArray snames)
  return $ (pullFrom snames n, snames)

pushG :: (TraverseExp a, ASize s) => Word32 -> TransformA
      -> Pull Word32 a -> Push Grid s a
pushG bs t (Pull l ixf) = Push (fromIntegral l) $ \wf ->
  ForAllBlocks (fromIntegral $ (l+bs-1) `div` bs) $ \bid ->
    ForAll (fromIntegral (min l bs)) $ \tid ->
      let gid = bid*(fromIntegral bs)+tid
      in wf (runTrans t bs l (ixf gid)) gid

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
