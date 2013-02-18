{-# LANGUAGE UndecidableInstances,
             FlexibleInstances
             #-}

module PExp (PExp, parameter, ToExp, toExp, ToPExp, toPExp, unsafeFromPExp) where

import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Data.Word



data PExp a = PMExp (Exp a)
    deriving (Show)

parameter :: (Scalar a) => Name -> PExp a 
parameter = PMExp . variable

class (Num a, Integral a) => ToExp a where
    toExp :: a -> Exp Word32

instance ToExp Word32 where
    toExp a = Literal a

instance ToExp (PExp Word32) where
    toExp (PMExp a) = a

instance ToExp (Exp Word32) where
    toExp a = a

class (ToExp a) => ToPExp a where
    toPExp :: a -> Word32 --should be a -> PExp Word32

instance ToPExp Word32 where
    toPExp a = a

instance ToPExp (PExp Word32) where
    toPExp a = unsafeFromPExp a

lift f (PMExp a) = PMExp $ f a
lift2 f (PMExp a) (PMExp b) = PMExp $ a `f` b

instance (Num (Exp a)) => Num (PExp a) where
    (+) = lift2 (+)
    (-) = lift2 (-)
    (*) = lift2 (*)
    abs = lift abs
    signum = lift signum
    fromInteger = PMExp . fromInteger

instance (Ord (Exp a)) => Ord (PExp a) where
    min = lift2 min
    max = lift2 max

instance (Eq (Exp a)) => Eq (PExp a) where
    (==) = undefined

instance (Real a, ToExp (PExp a), Integral (Exp a)) => Integral (PExp a) where
    mod = lift2 mod
    div = lift2 div
    quotRem = undefined
    toInteger = undefined

instance (Real (Exp a), Real a) => Real (PExp a) where
    toRational = toRational.unsafeFromPExp

instance (Enum (Exp a), ToExp (PExp a)) => Enum (PExp a) where
    toEnum = PMExp . toEnum
    fromEnum = fromEnum.toExp


--instance (Floating (Exp a)) => Floating (PExp a) where
--fractional
--scalar
--choice
--show
--bits

unsafeFromPExp (PMExp a) = evalConst a
evalConst (Literal a) = a

