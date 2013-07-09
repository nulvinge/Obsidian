{-# LANGUAGE GADTs,
             ExistentialQuantification,
             FlexibleInstances #-}

{- CodeGen.Program.

   Joel Svensson 2012, 2013

   Notes:
     2013-03-17: Codegeneration is changing
-} 


module Obsidian.CodeGen.Program where

import Obsidian.Exp
import Obsidian.Globs
import Obsidian.Types
import Obsidian.Atomic

import qualified Obsidian.Program as P
import Obsidian.Program (Step,Zero)

import Data.Word
import Data.Supply
import Data.List

import System.IO.Unsafe

---------------------------------------------------------------------------
-- New Intermediate representation
---------------------------------------------------------------------------

type IMList a = [(Statement a,a)]

type IM = IMList ()

-- out :: 
out a = [(a,())]


data Statement t =
  forall a. (Show a, Scalar a) => SAssign Name [Exp Word32] (Exp a)
  | forall a. (Show a, Scalar a) => SAtomicOp Name Name (Exp Word32) (Atomic a)
  | SCond (Exp Bool) (IMList t) 
  | SSeqFor String (Exp Word32) (IMList t)
  | SBreak
  | SSeqWhile (EBool) (IMList t)
    
  | SForAll (Exp Word32) (IMList t) 
  | SForAllBlocks (Exp Word32) (IMList t)

    -- a special loop over all threads..
  | SForAllThreads (Exp Word32) (IMList t)
    
    -- Memory Allocation..
  | SAllocate Name Word32 Type
  | SDeclare  Name Type
  | SOutput   Name Type

  | SComment String

    -- Synchronisation
  | SSynchronize

    
-- compileStep1 :: P.Program t a -> IM
-- compileStep1 p = snd $ cs1 ns p
--   where
--     ns = unsafePerformIO$ newEnumSupply


compileStep1 :: Compile t => P.Program t a -> IM
compileStep1 p = snd $ compile ns p
  where
    ns = unsafePerformIO$ newEnumSupply


class Compile t where
  compile :: Supply Int -> P.Program t a -> (a,IM)

-- Compile Thread program 
instance Compile Zero  where 
  compile s p = cs s p 

-- Compile Block program 
instance Compile (Step Zero) where
  compile s (P.ForAll n f) = (a,out (SForAll n im))
    where
      p = f (ThreadIdx X)
      (a,im) = compile s p
  compile s p = cs s p 

-- Compile a Grid Program 
instance Compile (Step (Step (Zero))) where
  compile s (P.ForAll n f) = (a, out (SForAllBlocks n im))
    where 
      p = f (BlockIdx X)
      (a,im) = compile s p
  compile s p = cs s p


---------------------------------------------------------------------------
-- General compilation
---------------------------------------------------------------------------
cs :: Compile t => Supply Int -> P.Program t a -> (a,IM) 
cs i P.Identifier = (supplyValue i, [])

cs i (P.Assign name ix e) =
  ((),out (SAssign name ix e))
 
cs i (P.AtomicOp name ix at) = (v,out im)
  where 
    nom = "a" ++ show (supplyValue i)
    v = variable nom
    im = SAtomicOp nom name ix at
      
cs i (P.Cond bexp p) = ((),out (SCond bexp im)) 
  where ((),im) = compile i p

cs i (P.SeqFor n f) = (a,out (SSeqFor nom n im))
  where
    (i1,i2) = split2 i
    nom = "i" ++ show (supplyValue i1)
    v = variable nom
    p = f v
    (a,im) = compile i2 p
cs i (P.SeqWhile b p) = (a, out (SSeqWhile b im))
  where
    (a,im) = compile i p

cs i (P.Break) = ((), out SBreak)

-- This should not happen, right ?                  
--cs i (P.ForAll n f) = (a,out (SForAll n im))
--  where
--    p = f (ThreadIdx X)  
--    (a,im) = compile i p 

-- This is trashed! 
--cs i (P.ForAllThreads n f) = (a,out (SForAllThreads n im)) 
--  where
--    p = f (BlockIdx X * BlockDim X + ThreadIdx X)
--    (a,im) = cs i p


cs i (P.Allocate id n t) = ((),out (SAllocate id n t))
cs i (P.Declare  id t)   = ((),out (SDeclare id t))
-- Output works in a different way! (FIX THIS!)
--  Uniformity! (Allocate Declare Output) 
cs i (P.Output   t)      = (nom,out (SOutput nom t))
  where nom = "output" ++ show (supplyValue i) 
cs i (P.Sync)            = ((),out (SSynchronize))
cs i (P.Comment c)       = ((),out (SComment c))


cs i (P.Bind p f) = (b,im1 ++ im2) 
  where
    (s1,s2) = split2 i
    (a,im1) = compile s1 p
    (b,im2) = compile s2 (f a)

cs i (P.Return a) = (a,[])

-- The nested ForAll case. 
cs i p = error $ show $ P.printPrg p -- compile i p 

---------------------------------------------------------------------------
-- Old cs1
--------------------------------------------------------------------------- 
-- cs1 :: Supply Int -> P.Program t a -> (a,IM) 
-- cs1 i P.Identifier = (supplyValue i, [])

-- cs1 i (P.Assign name ix e) =
--   ((),out (SAssign name ix e))
 
-- cs1 i (P.AtomicOp name ix at) = (v,out im)
--   where 
--     nom = "a" ++ show (supplyValue i)
--     v = variable nom
--     im = SAtomicOp nom name ix at
      
-- cs1 i (P.Cond bexp p) = ((),out (SCond bexp im)) 
--   where ((),im) = cs1 i p

-- cs1 i (P.SeqFor n f) = (a,out (SSeqFor nom n im))
--   where
--     (i1,i2) = split2 i
--     nom = "i" ++ show (supplyValue i1)
--     v = variable nom
--     p = f v
--     (a,im) = cs1 i2 p
-- cs1 i (P.SeqWhile b p) = (a, out (SSeqWhile b im))
--   where
--     (a,im) = cs1 i p

-- cs1 i (P.Break) = ((), out SBreak)
    
-- cs1 i (P.ForAll n f) = (a,out (SForAll n im))
--   where
--     p = f (ThreadIdx X)  
--     (a,im) = cs1 i p 

-- --cs1 i (P.ForAllBlocks n f) = (a,out (SForAllBlocks n im)) 
-- --  where
-- --    p = f (BlockIdx X)
-- --    (a,im) = cs1 i p


-- {- 
--    Warning: Every thread will ALWAYS need to perform a conditional
--        (Only in special case is the conditional not needed) 
--    TRY To express all library functions using ForAllBlocks + ForAll
--    For more flexibility and probably in the end performance.

--    If we only consider the limited form of Obsidian programs
--    Pull a1 -> Pull a2 -> ... -> Push Grid an
--    this is not a problem. But when we allow people to drop down to
--    the low level (like in counting sort, this is not general enough) 
-- -}     
-- cs1 i (P.ForAllThreads n f) = (a,out (SForAllThreads n im)) 
--   where
--     p = f (BlockIdx X * BlockDim X + ThreadIdx X)
--     (a,im) = cs1 i p


-- cs1 i (P.Allocate id n t) = ((),out (SAllocate id n t))
-- cs1 i (P.Declare  id t)   = ((),out (SDeclare id t))
-- -- Output works in a different way! (FIX THIS!)
-- --  Uniformity! (Allocate Declare Output) 
-- cs1 i (P.Output   t)      = (nom,out (SOutput nom t))
--   where nom = "output" ++ show (supplyValue i) 
-- cs1 i (P.Sync)            = ((),out (SSynchronize))


-- cs1 i (P.Bind p f) = (b,im1 ++ im2) 
--   where
--     (s1,s2) = split2 i
--     (a,im1) = cs1 s1 p
--     (b,im2) = cs1 s2 (f a)

-- cs1 i (P.Return a) = (a,[])


---------------------------------------------------------------------------
-- Analysis
--------------------------------------------------------------------------- 
numThreads :: IMList a -> Either Word32 (EWord32)
numThreads im = foldl maxCheck (Left 0) $ map process im
  where
    process (SCond bexp im,_) = numThreads im
    process (SSeqFor _ _ _,_) = Left 1
    process (SForAll (Literal n) _,_) = Left n
    process (SForAll n _,_) = Right n
    process (SForAllBlocks _ im,_) = numThreads im
    process (SForAllThreads n im,_) = Right (variable "UNKNOWN") --fix this!
    process a = Left 0 -- ok ? 

    maxCheck (Left a) (Right b)  = Right $ maxE (fromIntegral a) b
    maxCheck (Right a) (Left b)  = Right $ maxE a (fromIntegral b)
    maxCheck (Left a) (Left  b)  = Left  $ max a b
    maxCheck (Right a) (Right b) = Right $ maxE a b


getOutputs :: IMList a -> [(Name,Type)]
getOutputs im = concatMap process im
  where
    process (SOutput name t,_)      = [(name,t)]
    process (SSeqFor _ _ im,_)      = getOutputs im
    process (SForAll _ im,_)        = getOutputs im
    process (SForAllBlocks _ im,_)  = getOutputs im
    process (SForAllThreads _ im,_) = getOutputs im
    process a = []
    

---------------------------------------------------------------------------
-- Turning IM to strings
---------------------------------------------------------------------------

printIM :: Show a => IMList a -> String 
printIM im = concatMap printStm im
  
-- Print a Statement with metadata 
printStm :: Show a => (Statement a,a) -> String
printStm (SAssign name [] e,m) =
  name ++ " = " ++ printExp e ++ ";" ++ meta m
printStm (SAssign name ix e,m) =
  name ++ "[" ++ concat (intersperse "," (map printExp ix)) ++ "]" ++
  " = " ++ printExp e ++ ";" ++ meta m
printStm (SAtomicOp res arr ix op,m) =
  res ++ " = " ++
  printAtomic op ++ "(" ++ arr ++ "[" ++ printExp ix ++ "]);" ++ meta m
printStm (SAllocate name n t,m) =
  name ++ " = malloc(" ++ show n ++ ");" ++ meta m
printStm (SDeclare name t,m) =
  show t ++ " " ++ name ++ ";" ++ meta m
printStm (SOutput name t,m) =
  show t ++ " " ++ name ++ ";" ++ meta m
printStm (SCond bexp im,m) =
  "if " ++ show bexp ++ "{\n" ++ 
  concatMap printStm im ++ "\n};" ++ meta m

printStm (SSynchronize,m) =
  "sync();" ++ meta m
  
printStm (SSeqFor name n im,m) =
  "for " ++ name  ++ " in [0.." ++ show n ++"] do" ++ meta m ++ 
  concatMap printStm im ++ "\ndone;\n"

printStm (SForAll n im,m) =
  "forAll i in [0.." ++ show n ++"] do" ++ meta m ++
  concatMap printStm im ++ "\ndone;\n"

printStm (SForAllBlocks n im,m) =
  "forAllBlocks i in [0.." ++ show n ++"] do" ++ meta m ++
  concatMap printStm im ++ "\ndone;\n"
printStm (SForAllThreads n im,m) =
  "forAllThreads i in [0.." ++ show n ++"] do" ++ meta m ++ 
  concatMap printStm im ++ "\ndone;\n"


  
-- printStm (a,m) = error $ show m 

meta :: Show a => a -> String
meta m = "\t//" ++ show m ++ "\n" 
