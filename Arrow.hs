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
import Data.List (genericIndex)

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

instance Show (a :-> b) where
  show (Pure f) = "Pure f"
  show (Sync f g) = "Sync f (" ++ show g ++ ")"

instance Category (:->) where
  id = Pure id

  (.) (Pure f) (Pure g)   = Pure (f . g)
  (.) (Pure f) (Sync h g) = Sync h (Pure f . g)
  (.) (Sync h g) (Pure f) = Sync (h . f) g
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
  left (Pure f) = Pure (either (Left . f) (Right . id))



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

type RunInfo b c d = (Word32, ((Pull Word32 (Exp b),d) :-> c), Pull Word32 (Exp b), d)
type Transform = forall e. (Scalar e) => (Word32 -> Exp e -> Exp e)

run :: Word32 -> (a :-> b) -> a -> GProgram b
run bs a = run' bs (const id) a

run' :: Word32 -> Transform -> (a :-> b) -> a -> GProgram b
run' bs t (Pure f)   a = do
  --forceG (resize (fromIntegral (len (f a))) (push Grid (f a)))
  return (f a)
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
     -> RunInfo b c d -> (Word32 -> Exp b -> Exp b)
     -> BProgram (Pull Word32 (Exp b), Transform)
runB bid ri@(bs,_,Pull l ixf,_) t =
  if runWable ri
    then runW bid ri t
    else do
      a'' <- force a'
      return (a'', divide (getName a'') bs)
  where a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                      wid = simplifyMod bs (min bs l) gid
                  in wf (t (min bs l) (ixf gid)) wid

getName :: Pull Word32 (Exp a) -> Name
getName (Pull n ixf) = let Index (n,_) = ixf (Literal 0)
                       in n

collectRun :: (forall c. Exp c -> [d]) -> Exp Word32 -> (a :-> b) -> a -> [d]
collectRun cf ix (Pure f)   a = [] --cf (f a)
collectRun cf ix (Sync f g) a =
  let (a'@(Pull n ixf),d) = f a
      e = ixf ix
      a'' = fakeForce a' "noname"
  in (cf e) ++ collectRun cf ix g (a'',d)

isDivable m bs n a = (simplifyDiv m bs n a) == (Literal 0)

runWable :: (Scalar b) => RunInfo b c d -> Bool
runWable ri@(bs,g,a,d) =
  let n = "target"
      gid = (BlockIdx X*(fromIntegral bs) +(ThreadIdx X))
      a' = fakeForce a n
      accesses = collectRun (collectExp (getIndice n) (++)) gid g (a',d)
  in all (isDivable 32 bs (len a)) accesses

runW :: (Scalar b)
     => Exp Word32
     -> RunInfo b c d -> (Word32 -> Exp b -> Exp b)
     -> BProgram (Pull Word32 (Exp b), Transform)
runW bid ri@(bs,_,Pull l ixf,_) t = do
    a'' <- write a'
    return (a'', divide (getName a'') 32)
  where a' = Push l $ \wf ->
               ForAll (sizeConv l) $ \tid ->
                  let gid = bid*(fromIntegral bs)+tid
                      wid = simplifyMod 32 (min bs l) gid
                  in wf (t (min bs l) (ixf gid)) wid

divide :: (Scalar b)
       => Name -> Word32
       -> Word32 -> Exp b -> Exp b
divide n m bsl = traverseExp (traverseOnIndice n f)
  where f = strace.simplifyMod m bsl


testInput :: Pull Word32 (Exp Int)
testInput = namedGlobal "apa" 2048

testInput' :: Pull (Exp Word32) (Exp Int)
testInput' = namedGlobal "apa" 2048

liftE a = resize (fromIntegral (len a)) a

reduce0 :: (Scalar a, Num (Exp a)) => Word32 -> (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce0 1 = id
reduce0 n = reduce0 (n`div`2) <<< aSync <<^ (uncurry (zipWith (+)) <<< halve)
tr0 = quickPrint t testInput
  where s a = liftG $ simpleRun (reduce0 (len a)) a
        t a = run 1024 (reduce0 (len a)) a 

reduce0' :: Word32 -> (Pull Word32 (Exp Int) :-> (Pull Word32 (Exp Int)))
reduce0' = reduce0

reduce1 :: (Scalar a, Num (Exp a)) => (Pull Word32 (Exp a) :-> (Pull Word32 (Exp a)))
reduce1 = Pure (halve >>> uncurry (zipWith (+))) >>>
    Pure (\a' -> trace (show (len a')) a') >>>
  proc a -> do
    if len a == 1
      then returnA -< a
      else reduce1 <<< aSync -< a
tr1 = quickPrint (run 1024 reduce1) testInput


