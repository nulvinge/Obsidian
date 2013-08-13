{-# LANGUAGE FlexibleInstances,
             TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables #-}

module Obsidian.Num
  (Log,Precise,toLog,fromLog
  ,Compensated,Compensable,toCompensated,fromCompensated
  ) where

import Obsidian.Exp
import Obsidian.Memory
import Data.Word
import Numeric.Log as Log
import Numeric.Compensated as C

--very unsafe
instance (Scalar a,Floating a, RealFloat a) => RealFloat (Exp a) where
  isInfinite a = False
  floatRadix = error "no RealFloat for Float yet"
  floatDigits = error "no RealFloat for Float yet"
  floatRange = error "no RealFloat for Float yet"
  decodeFloat = error "no RealFloat for Float yet"
  encodeFloat = error "no RealFloat for Float yet"
  isNaN a = False
  isDenormalized a = False
  isNegativeZero a = False
  isIEEE a = False

instance (Scalar a,RealFrac a) => RealFrac (Exp a) where
  properFraction a = error "no RealFrac for Float yet"

-- Log

instance (Scalar a, Floating a) => Precise (Exp a) where
  log1p = UnOp Log1p
  expm1 = UnOp Expm1

instance (MemoryOps a) => MemoryOps (Log a) where
  createNames a = createNames (undefined :: a)
  assignArray n (Log.Exp a) i = assignArray n a i
  assignScalar n (Log.Exp a) = assignScalar n a
  pullFrom n s = fmap Log.Exp $ pullFrom n s
  readFrom n = Log.Exp $ readFrom n

toLog :: (Floating a,Precise a) => a -> Log a
toLog = Log.Exp . exp
fromLog :: (Floating a,Precise a) => Log a -> a
fromLog = log . ln

-- Compensated

instance (Compensable a,Scalar a) => Compensable (Exp a) where
  data Compensated (Exp a) = CE (Exp a) (Exp a)
  with (CE a b) k = k a b
  compensated = CE
  magic = Literal magic

instance (Compensable a,MemoryOps a) => MemoryOps (Compensated a) where
  createNames a = createNames (undefined :: (a,a))
  assignArray n c i = with c $ \a b -> assignArray n (a,b) i
  assignScalar n c = with c $ \a b -> assignScalar n (a,b)
  pullFrom n s =  fmap (uncurry compensated) $ pullFrom n s
  readFrom n = uncurry compensated $ readFrom n

toCompensated :: (Compensable a) => a -> Compensated a
toCompensated a = compensated a 0

fromCompensated :: (Compensable a) => Compensated a -> a
fromCompensated = uncompensated

