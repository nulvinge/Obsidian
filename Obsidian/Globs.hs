
{- Joel Svensson 2012 -} 

module Obsidian.Globs where


import Data.Word

---------------------------------------------------------------------------
-- Aliases

type Name = String

type NumThreads = Word32

data LoopLocationType = Kernel | Grid | Block | Thread | Vector
  deriving (Show,Eq,Ord,Enum,Bounded)
type PreferredLoopLocation = [(LoopLocationType,LoopType,Word32)]
data LoopType = Seq | Par
  deriving (Show,Eq)


