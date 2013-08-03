{-# LANGUAGE FlexibleInstances,
             ScopedTypeVariables #-}

module Obsidian.Log (Log,Precise,toLog,fromLog) where

import Obsidian.Exp
import Obsidian.Memory
import Data.Word
import Numeric.Log as Log

instance (Scalar a, Floating a) => Precise (Exp a) where
  log1p = UnOp Log1p
  expm1 = UnOp Expm1

instance (MemoryOps a) => MemoryOps (Log a) where
  createNames a = createNames (undefined :: a)
  assignArray n (Log.Exp a) i = assignArray n a i
  assignScalar n (Log.Exp a) = assignScalar n a
  pullFrom n s = fmap Log.Exp $ pullFrom n s
  readFrom n = Log.Exp $ readFrom n

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
  isIEEE a = True


instance (Scalar a,RealFrac a) => RealFrac (Exp a) where
  properFraction a = error "no RealFrac for Float yet"

toLog :: (Floating a,Precise a) => a -> Log a
toLog = Log.Exp . exp
fromLog :: (Floating a,Precise a) => Log a -> a
fromLog = log . ln

