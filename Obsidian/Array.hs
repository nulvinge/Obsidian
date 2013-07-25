{-# LANGUAGE MultiParamTypeClasses,  
             FlexibleInstances, FlexibleContexts,
             GADTs, 
             TypeFamilies,
             RankNTypes #-} 

{- Joel Svensson 2012

   Notes:
    2013-01-08: Removed number-of-blocks field from Distribs
    2012-12-10: Drastically shortened. 
-}

module Obsidian.Array where

import Obsidian.Exp 
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Program

import Data.List
import Data.Word

---------------------------------------------------------------------------
-- Aliases
---------------------------------------------------------------------------
type SPull = Pull Word32
type DPull = Pull EWord32

type SPush = Push Word32
type DPush = Push EWord32 
---------------------------------------------------------------------------
-- Create arrats
---------------------------------------------------------------------------
undefinedGlobal n = Pull n $ \gix -> undefined
namedGlobal name n = Pull n $ \gix -> index name gix
namedPull name n = Pull n $ \gix -> index name gix

---------------------------------------------------------------------------
-- Class ArraySize
--------------------------------------------------------------------------- 
class (Integral a, Num a, OrdE a) => ASize a where
  sizeConv :: a -> Exp Word32
  sizeEither :: a -> Either Word32 (Exp Word32)

instance ASize Word32 where
  sizeConv = fromIntegral
  sizeEither = Left

instance ASize (Exp Word32) where
  sizeConv = id 
  sizeEither = Right

---------------------------------------------------------------------------
-- Push and Pull arrays
---------------------------------------------------------------------------
data Push s a =
  Push s ((a -> EWord32 -> Program ()) -> Program ())

data Pull s a = Pull s (EWord32 -> a)

mkPushArray n p = Push n p 
mkPullArray n p = Pull n p  

class Array a where
  resize :: r -> a s e -> a r e
  len    :: ASize s => a s e -> s
  aMap   :: (e -> e') -> a s e -> a s e'
  ixMap  :: (Exp Word32 -> Exp Word32) -> a s e -> a s e
  
instance Array Pull where 
  resize m (Pull _ ixf) = Pull m ixf
  len      (Pull s _)   = s
  aMap   f (Pull n ixf) = Pull n (f . ixf)
  ixMap  f (Pull n ixf) = Pull n (ixf . f) 
  
instance Array Push where 
  resize m (Push _ p) = Push m p
  len      (Push s _) = s
  aMap   f (Push s p) = Push s $ \wf -> p (\e ix -> wf (f e) ix)
  ixMap  f (Push s p) = Push s $ \wf -> p (\e ix -> wf e (f ix))

class Indexible a where 
  access :: a s e -> Exp Word32 -> e 
  
instance Indexible Pull where
  access (Pull n ixf) ix = ixf ix

---------------------------------------------------------------------------
-- Functor instance Pull/Push arrays
---------------------------------------------------------------------------
instance Array arr => Functor (arr w) where 
  fmap = aMap


---------------------------------------------------------------------------
-- Pushable
---------------------------------------------------------------------------

class Pushable t where
  push :: ASize s => t s e -> Push s e 

instance Pushable Push where
  push = id

instance Pushable Pull where
  push arr = Push (len arr) $ \wf ->
              forAll (sizeConv (len arr)) $ \i ->
                wf (arr ! i) i

pushN :: (ASize s) => Word32 -> Pull s e -> Push s e
pushN n arr =
  Push (len arr) $ \ wf -> forAll (sizeConv ((len arr) `div` fromIntegral n)) $ \bix ->
    forAll (fromIntegral n) $ \tix -> wf (arr ! (bix * fromIntegral n + tix))
                                                (bix * fromIntegral n + tix) 

namedArray name n = mkPullArray n (\ix -> index name ix)
indexArray n      = mkPullArray n (\ix -> ix)

infixl 9 ! 
(!) :: Indexible a => a s e -> Exp Word32 -> e 
(!) = access

