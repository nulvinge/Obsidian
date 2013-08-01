{- Joel Svensson 2012,2013

   Notes:
   2013-04-02: Added a Break statement to the language.
               Use it to break out of sequential loops.
   2013-01-08: removed number-of-blocks field from ForAllBlocks

-}

{-# LANGUAGE GADTs, TypeFamilies, EmptyDataDecls #-}
             


module Obsidian.Program  where 
 
import Data.Word
import Data.Monoid

import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Atomic

-- Package value-supply
import Data.Supply
import System.IO.Unsafe

import Data.Text

---------------------------------------------------------------------------
-- Thread/Block/Grid 
---------------------------------------------------------------------------

type Identifier = Int 

architecture =
  [-- (Kernel,0)
   (Block,65536)
  ,(Thread,1024)
  -- ,(Thread,0)
  ,(Vector,4)
  ]

---------------------------------------------------------------------------
-- Program datatype
--------------------------------------------------------------------------
data Program a where
  --Combiners
  For :: LoopType
      -> PreferredLoopLocation
      -> EWord32
      -> (EWord32 -> Program ())
      -> Program ()

  Cond     :: Exp Bool -> Program () -> Program ()
  SeqWhile :: Exp Bool -> Program () -> Program () 
  ParBind  :: Program a -> Program b -> Program (a,b)
  Return   :: a -> Program a
  Bind     :: Program a -> (a -> Program b) -> Program b

  --Statements
  Assign :: Scalar a
         => Name
         -> [Exp Word32]
         -> (Exp a)
         -> Program ()
           
  AtomicOp :: Scalar a
           => Name 
           -> Exp Word32
           -> Atomic a
           -> Program (Exp a)

  Identifier :: Program Identifier 
  Break      :: Program () 
  Allocate   :: Name -> Word32 -> Type -> Program () 
  Declare    :: Name -> Type -> Program () 
  Output     :: Type -> Program Name
  --Sync       :: Program ()
  Comment    :: String -> Program ()


---------------------------------------------------------------------------
-- Helpers 
--------------------------------------------------------------------------- 
uniqueSM = do
  id <- Identifier
  return $ "arr" ++ show id 

uniqueNamed pre = do
  id <- Identifier
  return $ pre ++ show id 

---------------------------------------------------------------------------
-- forAll 
---------------------------------------------------------------------------
forAll :: EWord32 -> (EWord32 -> Program ()) -> Program ()
forAll n f = For Par [] n f

---------------------------------------------------------------------------
-- SeqFor
---------------------------------------------------------------------------
seqFor :: EWord32 -> (EWord32 -> Program ()) -> Program ()
seqFor (Literal 1) f = f 0
seqFor n f = For Seq [] n f

forAllBlocks = forAll

---------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------
instance Monad (Program) where
  return = Return
  (>>=) = Bind

---------------------------------------------------------------------------
-- runPrg (RETHINK!) (Works for Block programs, but all?)
---------------------------------------------------------------------------
runPrg :: Int -> Program a -> (a,Int)
runPrg i Identifier = (i,i+1)

-- Maybe these two are the most interesting cases!
-- Return may for example give an array. 
runPrg i (Return a) = (a,i)
runPrg i (Bind m f) =
  let (a,i') = runPrg i m
  in runPrg i' (f a)
     
runPrg i (For t [] n ixf) =
  let (p,i') = runPrg i (ixf (variable "tid")) 
  in  (p,i')
-- What can this boolean depend upon ? its quite general!
--  (we know p returns a ()... ) 
runPrg i (Cond b p) = ((),i) 
runPrg i (Declare _ _) = ((),i)
runPrg i (Allocate _ _ _ ) = ((),i)
runPrg i (Assign _ _ a) = ((),i) -- Probaby wrong.. 
runPrg i (AtomicOp _ _ _) = (variable ("new"++show i),i+1)

{- What do I want from runPrg ?

   # I want to it to "work" for all block programs (no exceptions)
   # I want a BProgram (Pull a) to return a Pull array of "correct length)
-}

                            
---------------------------------------------------------------------------
-- printPrg (REIMPLEMENT) xs
---------------------------------------------------------------------------
printPrg prg = (\(_,x,_) -> x) $ printPrg' 0 prg

printPrg' :: Int -> Program a -> (a,Text,Int)
printPrg' i Identifier = (i,pack "getId;\n",i+1) 
-- printPrg' i Skip = ((),";\n", i)
printPrg' i (Assign n ix e) =
  ((),pack $ n ++ "[" ++ show ix ++ "] = " ++ show e ++ ";\n", i) 
printPrg' i (AtomicOp n ix e) =
  let newname = "r" ++ show i
  in (variable newname, pack $
      newname ++ " = " ++ printAtomic e ++
      "( " ++ n ++ "[" ++ show ix ++ "])\n",i+1)
printPrg' i (Allocate id n t) =
  let newname = id -- "arr" ++ show id
  in ((),pack $ newname ++ " = malloc(" ++ show n ++ ");\n",i+1)
printPrg' i (Declare id t) =
  let newname = id -- "arr" ++ show id
  in ((),pack $ show t ++ " " ++ newname ++ "\n",i+1)
printPrg' i (Cond p f) =
  let (a,prg2,i') = printPrg' i f
  in ( a,pack ("if (" ++ show p ++  ")" ++ "{\n")
         `append` prg2
         `append` pack "\n}",
       i')
printPrg' i (For t pl n f) =
  let (a,prg2,i') = printPrg' i (f (variable "i"))
  in ( a, pack (show t ++ "for (i in 0.." ++ show n ++ ") " ++ (show pl) ++ " {\n")
          `append` prg2
          `append` pack "\n}",
       i')
printPrg' i (Return a) = (a,pack "MonadReturn;\n",i)
printPrg' i (Bind m f) =
  let (a1, str1,i1) = printPrg' i m
      (a2,str2,i2) = printPrg' i1 (f a1)
  in (a2,str1 `append` str2, i2)

