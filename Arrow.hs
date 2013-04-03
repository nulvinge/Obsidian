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

instance Show (a :-> b) where
  show (Pure f) = "Pure f"
  show (Sync f g) = "Sync f (" ++ show g ++ ")"

instance Category (:->) where
  id = Pure id

  (.) (Pure f) (Pure g)   = Pure (f . g)
  (.) (Sync h g) (Pure f) = Sync (h . f) g
  --(.) (Pure f) (Sync h g) = Sync h (Pure f . g)
  (.) o (Sync h g)        = Sync h (o . g)

instance Arrow (:->) where
  arr = Pure
  --(***) (Pure f) (Pure g) = Pure $ \(x,y) -> (f x, g y)
  --(***) (Pure f) (Sync h g) = Sync t (r g)
  --  where t (a,d) = let (b,d') = h a
  --                  in (b,(d,d'))
  --        r = undefined
  --(***) (Pure f) (Pure g) = Pure $ \(x,y) -> (f x, g y)

  first (Pure f) = Pure (mapFst f)
    where mapFst f (a,b) = (f a, b)
  first (Sync h g) = Sync t (r g)
    where t (a,d) = let (b,d') = h a
                    in (b,(d,d'))
          r :: ((Pull Word32 (Exp b),d') :-> c)
            -> ((Pull Word32 (Exp b),(d,d')) :-> (c,d))
          r g = first g . (Pure $ \(a,(d,d')) -> ((a,d'),d))
  --first (Sync h g) = Pure $ \(a,b) -> ((Sync h g,a), b)

{-
instance ArrowApply (:->) where
  app = Pure $ (uncurry app')
    where app' :: (a :-> b) -> a -> b
          app' arr a =
            case arr of
              Pure f   -> f a
              Sync h g -> app' g (h a)
-}

instance ArrowChoice (:->) where
  left f  = f +++ id
  right f = id +++ f
  f +++ g = (f >>> arr Left) ||| (g >>> arr Right)
  (Pure f) ||| (Pure g) = arr (either f g)

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

type RunInfo b c d = (Word32, ((Pull Word32 (Exp b),d) :-> Pull Word32 (Exp c)), Pull Word32 (Exp b), d)
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

run' :: Word32 -> TransformA -> (a :-> Pull Word32 (Exp b)) -> a -> GProgram (Pull Word32 (Exp b), TransformA)
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

collectRun :: (forall c. Exp c -> [d]) -> Exp Word32 -> (a :-> (Pull Word32 (Exp b))) -> a -> [(Word32,d)]
collectRun cf ix (Pure f)   a = case f a of Pull n ixf -> addTup n (cf $ ixf ix)
--collectRun cf ix (Pure f)   a = [] --cf (f a)
collectRun cf ix (Sync f g) a =
  let (a'@(Pull n ixf),d) = f a
      a'' = fakeForce a' "noname"
  in addTup n (cf $ ixf ix) ++ collectRun cf ix g (a'',d)

isDivable :: Word32 -> Word32 -> Word32 -> Exp Word32 -> (Word32, Exp Word32) -> Bool
isDivable m bs ngid gid (na,a) = (simplifyDiv m bs na a) == (simplifyDiv m bs ngid gid) 

runAable :: (Scalar b) => (Exp Word32 -> (Word32,Exp Word32) -> Bool) -> RunInfo b c d -> Bool
runAable f ri@(bs,g,a,d) =
  let n = "target"
      gid = (BlockIdx X*(fromIntegral bs) +(ThreadIdx X))
      a' = fakeForce a n
      accesses = collectRun (collectExp (getIndice n) (++)) gid g (a',d)
  in accesses /= [] && all (gid `f`) accesses

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
  where f = simplifyMod 32
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
  return (Pull (len a) $ \_ -> Index (n,[]), const id)

divide :: (Scalar b)
       => Name -> (Word32 -> Exp Word32 -> Exp Word32)
       -> Word32 -> Exp b -> Exp b
divide n f bsl = traverseExp (traverseOnIndice n (f bsl))


testInput :: Pull Word32 (Exp Int)
testInput = namedGlobal "apa" 2048

testInput' :: Pull (Exp Word32) (Exp Int)
testInput' = namedGlobal "apa" 2048

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
          b <- if len a == 1
                then id -< a'
                else {- reduce2 <<< -} aSync -< a'
      returnA -< b
tr2 = quickPrint (run 1024 reduce2) testInput


