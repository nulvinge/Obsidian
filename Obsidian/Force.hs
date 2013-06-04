
{-# LANGUAGE MultiParamTypeClasses,
             FlexibleInstances,
             ScopedTypeVariables,
             TypeFamilies,
             GADTs  #-}

{- Joel Svensson 2012, 2013 

   Notes:

   2013-01-27: globArrays nolonger exist
   2013-01-02: Added simple forceG for globArrays
   2012-12-10: Edited 

-}

--  write_ should be internal use only
module Obsidian.Force (write,
                       force,
                       forceG,
                       forceG',
                       idSync
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

write :: forall p a. (Array p, Pushable p, MemoryOps a) => p Word32 a -> BProgram (Pull Word32 a)
write arr = do 
  snames <- names (undefined :: a)

  -- Here i know that this pattern match will succeed
  let n = len arr
  
  allocateArray snames n

  let (Push m p) = push Block arr

  p (assignArray snames) 
      
  return $ pullFrom snames n

idSync a = do
  Sync
  return a
  
force :: forall p a. (Array p, Pushable p, MemoryOps a) =>  p Word32 a -> BProgram (Pull Word32 a)
force arr = write arr >>= idSync

-- Experimental forceG  (Generalize!) 
forceG :: forall a. Scalar a
          => Push Grid (Exp Word32) (Exp a)
          -> GProgram () -- Really to something else (named output ?)
forceG (Push _ p)  =
  do
    output <- Output $ Pointer (typeOf (undefined :: Exp a))
    p (assignTo output) 
    return ()
    where
      assignTo nom a ix = Assign nom [ix] a 

-- Experimental general forceG
forceG' :: forall a. MemoryOps a
          => Push Grid Word32 a
          -> GProgram () -- Really to something else (named output ?)
forceG' a@(Push s p)  =
  do
    output <- outputArray a
    --output <- allocateArray n v s
    p (assignArray output)
    return ()
    where
      assignTo nom a ix = Assign nom [ix] a 

