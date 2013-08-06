
{- Joel Svensson 2012 -} 

module Obsidian.Globs where


import Data.Word

---------------------------------------------------------------------------
-- Aliases

type Name = String

type NumThreads = Word32

data LoopLocation = Unknown | Kernel | Grid | Block | Thread | Vector
  deriving (Show,Eq,Enum,Bounded)

instance Ord LoopLocation where
  compare Unknown _ = EQ
  compare _ Unknown = EQ
  compare a b = fromEnum a `compare` fromEnum b

type PreferredLoopLocation = [(LoopLocation,LoopType,Word32)]
data LoopType = Seq | Par
  deriving (Show,Eq)


