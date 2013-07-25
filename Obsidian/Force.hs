{-# LANGUAGE ScopedTypeVariables,
             FlexibleInstances #-}


{- Joel Svensson 2012, 2013 

   Notes: 
   2013-05-02: Removing things to do with forceG
               Removed the extensions (no longer needed) 
   2013-04-27: Something is broken. 
   2013-04-10: Looking at force and threads
   2013-01-27: globArrays nolonger exist
   2013-01-02: Added simple forceG for globArrays
   2012-12-10: Edited 

-}

--  write_ should be internal use only
module Obsidian.Force (force
                      ,unsafeForce
                      ) where

import Obsidian.Program
import Obsidian.Exp
import Obsidian.Array
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Memory

import Data.Word
---------------------------------------------------------------------------
-- Force local (requires static lengths!) 
---------------------------------------------------------------------------

force :: (Pushable t, MemoryOps a) => t Word32 a -> Program (Pull Word32 a)
force arr = do 
  let Push m p = push arr
  snames <- names (valType arr)
  allocateArray snames  m
  p (assignArray snames) 
  return $ pullFrom snames m

--does not do anything different from force
unsafeForce :: MemoryOps a => SPull a -> Program (SPull a) 
unsafeForce arr | len arr <= 32 = force (push arr) 
unsafeForce arr = force (push arr)

