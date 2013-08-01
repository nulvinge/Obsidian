{-# LANGUAGE GADTs,
             ExistentialQuantification,
             FlexibleInstances #-}

module Obsidian.CodeGen.Program where

import Obsidian.Exp
import Obsidian.Globs
import Obsidian.Types
import Obsidian.Atomic

import qualified Obsidian.Program as P

import Data.Word
import Data.Supply
import Data.List
import Data.Maybe

import System.IO.Unsafe

---------------------------------------------------------------------------
-- New Intermediate representation
---------------------------------------------------------------------------

type IMList a = [(Statement a,a)]

type IM = IMList ()

-- out :: 
out a = [(a,())]

data Statement t
  --Combiners
  = SFor LoopType (Maybe LoopLocationType) Name EWord32 (IMList t) 
  | SCond (Exp Bool) (IMList t) 
  | SSeqWhile (EBool) (IMList t)
  | SPar [(IMList t)]

  --Statements
  | forall a. (Show a, Scalar a) => SAssign Name [Exp Word32] (Exp a)
  | forall a. (Show a, Scalar a) => SAtomicOp Name Name (Exp Word32) (Atomic a)
  | SBreak
    -- Memory Allocation..
  | SAllocate Name Word32 Type
  | SDeclare  Name Type
  | SOutput   Name Type
  | SComment String
  | SSynchronize

instance Show (Statement t) where
  show (SFor  l p n _ _) = "SFor " ++ show l ++ " " ++ show p
  show (SCond       _ _) = "SCond"
  show (SSeqWhile   _ _) = "SSeqWhile"
  show (SPar          _) = "SPar"
  show (SAssign _ _   _) = "SAssign"
  show (SAtomicOp _ _ _ _) = "SAtomicOp"
  show (SBreak)          = "SBreak"
  show (SAllocate _ _ _) = "SAllocate"
  show (SDeclare    _ _) = "SDeclare"
  show (SOutput     _ _) = "SOutput"
  show (SComment      _) = "SComment"
  show (SSynchronize   ) = "SSynchronize"

-- compileStep1 :: P.Program t a -> IM
-- compileStep1 p = snd $ cs1 ns p
--   where
--     ns = unsafePerformIO$ newEnumSupply


compileStep1 :: P.Program a -> IM
compileStep1 p = snd $ compile ns p
  where
    ns = unsafePerformIO$ do
      a <- newEnumSupply
      b <- newEnumSupply
      return (a,b)

type VarSupply = (Supply Int, Supply Int)

supplyVar    (a,b) = supplyValue a
supplyOutput (a,b) = supplyValue b
supplySplit (a,b) = ((a1,b1),(a2,b2))
  where (a1,a2) = split2 a
        (b1,b2) = split2 b

compile :: VarSupply -> P.Program a -> (a,IM)
--compile s (P.For t pl n f) = (a,out (SFor var t pl n im))
compile s (P.For t pl (Literal n) ff) = (a,fors)
    where
      (s1,s2) = supplySplit s
      var = "i" ++ show (supplyVar s2)

      forFs = zip (makeFor pl n) $ map (((var++"s")++).show) [0..]
      fors :: IM
      (fors,(a,im)) =
        case forFs of
          []  -> error "no fors"
          [((t,l,s),_)] -> (out $ SFor t l var (fromIntegral s) im
                           ,compile s1 $ ff (variable var))
          ffs           -> (foldr (\((t,l,s),n) li -> out $ SFor t l n (fromIntegral s) li) im ffs
                           ,compile s1 $ ff exp)
          {-
          ffs ->(foldr (\(f,n) li -> f n li) single
                $zip ffs names
                ,compile s1 $ ff (variable var))
          -}
      (texp,oexp) = partition (\((t,l,_),_) -> t == Par && l==Just Thread) $ forFs
      exp :: EWord32
      exp = foldl (\eb ((_,_,s),n) -> eb * fromIntegral s + variable n) 0 $ oexp ++ texp
      single :: IM
      single = (SDeclare var Word32,())
              : (SAssign var [] exp,())
              : im

      makeFor a  0 = error "zero loop"
      makeFor [] n = [(Par,Nothing,n)]
      makeFor a  1 = [(Par,Nothing,1)]
      makeFor ((l,t,s):r) n | s == 0 || n<=s = [(t,Just l,n)]
      makeFor ((l,t,s):r) n | n`mod`s == 0
        = (t,Just l,s)
        : if n`div`s == 1
            then []
            else makeFor r (n`div`s)

compile s p = cs s p 

---------------------------------------------------------------------------
-- General compilation
---------------------------------------------------------------------------
cs :: VarSupply -> P.Program a -> (a,IM) 
cs i P.Identifier = (supplyVar i, [])

cs i (P.Assign name ix e) =
  ((),out (SAssign name ix e))
 
cs i (P.AtomicOp name ix at) = (v,out im)
  where 
    nom = "a" ++ show (supplyVar i)
    v = variable nom
    im = SAtomicOp nom name ix at
      
cs i (P.Cond bexp p) = ((),out (SCond bexp im)) 
  where ((),im) = compile i p

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
  where nom = "output" ++ show (supplyOutput i) 
cs i (P.Comment c)       = ((),out (SComment c))

cs i (P.ParBind a b) = ((a',b'),out $ SPar [ima, imb])
  where (s1,s2) = supplySplit i
        (a',ima) = compile s1 a
        (b',imb) = compile s2 b

cs i (P.Bind p f) = (b,im1 ++ im2) 
  where
    (s1,s2) = supplySplit i
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
    process (SFor Seq _ _ _ _,_) = Left 1
    process (SFor Par (Just Thread) _ (Literal n) _,_) = Left n
    process (SFor Par (Just Thread) _ n _,_) = Right n
    process (SFor Par _ _              n im,_) = numThreads im
    process a = Left 0 -- ok ? 

    maxCheck (Left a) (Right b)  = Right $ maxE (fromIntegral a) b
    maxCheck (Right a) (Left b)  = Right $ maxE a (fromIntegral b)
    maxCheck (Left a) (Left  b)  = Left  $ max a b
    maxCheck (Right a) (Right b) = Right $ maxE a b


getOutputs :: IMList a -> [(Name,Type)]
getOutputs im = concatMap process im
  where
    process (SOutput name t,_)      = [(name,t)]
    process (SFor _ _ _ _ im,_)     = getOutputs im
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
  
printStm (SFor t name pl n im,m) =
  "for" ++ (show t) ++ " " ++ show name  ++ " in [0.." ++ show n ++"] do" ++ meta m ++ 
  concatMap printStm im ++ "\ndone;\n"
printStm (a,m) = show a ++ meta m

-- printStm (a,m) = error $ show m 

meta :: Show a => a -> String
meta m = "\t//" ++ show m ++ "\n" 

