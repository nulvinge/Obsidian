{-# LANGUAGE GADTs #-}

{- Joel Svensson,
   Josef Svenningsson
   2012 -} 
module Obsidian.Atomic where

import Obsidian.Exp

       

---------------------------------------------------------------------------
-- Atomic operations 
---------------------------------------------------------------------------
data Atomic a where
  AtomicInc :: Atomic (Data Int)

printAtomic AtomicInc = "atomicInc"