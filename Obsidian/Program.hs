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
import Data.List
import Data.Text (pack,unpack,Text,append)

-- Package value-supply
import Data.Supply
import System.IO.Unsafe

import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Atomic
import Obsidian.Helpers


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
      -> LoopLocation
      -> EWord32
      -> (EWord32 -> Program ())
      -> Program ()

  WithStrategy :: PreferredLoopLocation -> Program a -> Program a

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
forAll n f = For Par Unknown n f

---------------------------------------------------------------------------
-- SeqFor
---------------------------------------------------------------------------
seqFor :: EWord32 -> (EWord32 -> Program ()) -> Program ()
seqFor (Literal 1) f = f 0
seqFor n f = For Seq Unknown n f

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
     
runPrg i (For _ _ n ixf) =
  let (p,i') = runPrg i (ixf (variable "tid")) 
  in  (p,i')
-- What can this boolean depend upon ? its quite general!
--  (we know p returns a ()... ) 
runPrg i (Cond b p) = ((),i) 
runPrg i (Declare _ _) = ((),i)
runPrg i (Allocate _ _ _ ) = ((),i)
runPrg i (Assign _ _ a) = ((),i) -- Probaby wrong.. 
runPrg i (AtomicOp _ _ _) = (variable ("new"++show i),i+1)
runPrg i (WithStrategy _ a) = runPrg i a

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
         `append` pack "\n}\n",
       i')
printPrg' i (WithStrategy s f) =
  let (a,prg2,i') = printPrg' i f
  in ( a,pack ("WithStrategy " ++ show s ++ " {\n")
         `append` prg2
         `append` pack "\n}\n",
       i')
printPrg' i (For t pl n f) =
  let (a,prg2,i') = printPrg' i (f (variable "i"))
  in ( a, pack (show t ++ "for (i in 0.." ++ show n ++ ") " ++ (show pl) ++ " {\n")
          `append` prg2
          `append` pack "\n}\n",
       i')
printPrg' i (Return a) = (a,pack "MonadReturn;\n",i)
printPrg' i (Bind m f) =
  let (a1, str1,i1) = printPrg' i m
      (a2,str2,i2) = printPrg' i1 (f a1)
  in (a2,str1 `append` str2, i2)

-- b = [lix] -> Program ()
-- a = [lts]
-- (a -> ([lix] -> Program) -> ([lix] -> Program))

preferredFor :: PreferredLoopLocation -> EWord32 -> (EWord32 -> Program ()) -> Program ()
preferredFor [] n ll = For Par Unknown n ll
preferredFor pl n ll = fst $ splitLoop pl n f ll
  where f (t,l,i,s) li lix = For t l s (\ix -> li ((t,l,s,ix):lix))

splitLoop :: PreferredLoopLocation -> EWord32
     -> ((LoopType, LoopLocation, Int, EWord32)
         -> ([(LoopType, LoopLocation, EWord32, EWord32)] -> a)
         -> [(LoopType, LoopLocation, EWord32, EWord32)]
         -> a)
     -> (EWord32 -> a) 
     -> (a,[(LoopType, LoopLocation, EWord32)])
splitLoop pl n f ll = (fors [],map (\(t,l,i,e) -> (t,l,e)) forFs)
  where
    forFs = map (\(i,a@((t,l,_):_)) -> (t,l,i, product $ map (\(_,_,s) -> s) a))
          $ zip [0..]
          $ groupBy (\(t,l,_) (t',l',_) -> t==t' && l==l')
          $ sortBy snd3comp
          $ splitLoopInfo pl n
    fors = foldr f
                 (\lix -> ll $ makeExp lix)
                 forFs
    makeExp lix = foldl (\eb (_,_,s,ix) -> eb * s + ix) 0 $ oexp ++ texp
      where (texp,oexp) = partition (\(t,l,_,_) -> t == Par && l==Thread) lix

    snd3comp (t1,l1,_) (t2,l2,_) | l1 == l2 =
      case (t1,t2) of
        (Par,Par) -> EQ
        (Par,Seq) -> LT
        (Seq,Par) -> GT
        (Seq,Seq) -> EQ
    snd3comp (_,l1,_) (_,l2,_) = compare l1 l2

    splitLoopInfo :: PreferredLoopLocation -> Exp Word32 -> [(LoopType,LoopLocation,EWord32)]
    splitLoopInfo a (Literal 0) = error "zero loop"
    splitLoopInfo [] n = [(Seq,Unknown,n)]
    -- splitLoopInfo a  1 = [(Par,Unknown,1)]
    splitLoopInfo ((t,l,s):r) (Literal n) | n <= s = [(t,l,fromIntegral n)]
    splitLoopInfo ((t,l,s):r) n | s == 0 = [(t,l,n)]
    splitLoopInfo ((t,l,s):r) n | m > 1
      = (t,l,fromIntegral m)
      : case linerizel $ n`div`Literal m of
          []      -> []
          [(1,1)] -> []
          _       -> splitLoopInfo r (n`div`fromIntegral m)
      where m = s `gcd` (fromInteger $ maxDivable n)
    splitLoopInfo ((t,l,0):r) n = [(t,l,n)]
    splitLoopInfo (_:r) n = splitLoopInfo r n

