{-# LANGUAGE FlexibleInstances,
             OverlappingInstances,
             UndecidableInstances,
             FlexibleContexts,
             MultiParamTypeClasses,
             TypeOperators,
             TypeFamilies ,
             ScopedTypeVariables
             #-}

{- Joel Svensson 2012, 2013
   Niklas Ulvinge 2013

  Notes:

  2013-04-28: Big Changes. Allows empty lists of inputs
              that are represented by ().
              TODO: Add Niklas modifications that allow tuples in input arrays.

  2013-01-24: Changes with the new Array types in mind
  2013-01-08: Edited
  2012-12-10: Edited

-} 


module Obsidian.CodeGen.InOut where 

import Obsidian.Exp 
import Obsidian.Array

import Obsidian.Types
import Obsidian.Globs 
import Obsidian.Program
import Obsidian.Force
import Obsidian.Memory
import Obsidian.Helpers

import qualified Obsidian.CodeGen.Program as CG 

import Data.Word
import Data.Int
import Data.Char
      
---------------------------------------------------------------------------
-- New approach (hopefully)
---------------------------------------------------------------------------
-- "reify" Haskell functions into CG.Programs

{-
   Blocks needs to be of specific sizes (a design choice we've made).
   Because of this a prototypical input array needs to be provided
   that has a static block size (the number of blocks is dynamic).

   To make things somewhat general a heterogeneous list of input arrays
   that has same shape as the actual parameter list of the function
   is passed into toProgram (the reifyer). 

-} 

type Inputs = [(Name,Type)]
type ArraySizes = [(Name,EWord32)]

class ToProgram a where
  toProgram :: Int -> a -> InputList a -> (Inputs,ArraySizes,CG.IM)

class GetTypes a where
  getTypes :: a -> Name -> (Inputs,ArraySizes,a)

instance (MemoryOps a) => GetTypes (Pull Word32 a) where
  getTypes a name = (typesArray names
                    ,map (\n -> (n,sizeConv $ len a)) (getNames names)
                    ,pullFrom names (len a))
      where names = createNames (valType a) name

instance (MemoryOps a) => GetTypes (Pull (Exp Word32) a) where
  getTypes a name = ((typesArray names) ++ [(namen, Word32)]
                    ,(map (\n -> (n,nvar)) (getNames names)) ++ [(namen,0)]
                    ,pullFrom names nvar)
      where namen = name ++ "n"
            nvar = variable namen * (fromIntegral $ maxDivable $ len a)
            names = createNames (valType a) name

instance (Scalar a) => GetTypes (Exp a) where
  getTypes a name = (typesScalar names
                    ,map (\n -> (n,0)) (getNames names)
                    ,readFrom names)
      where names = createNames a name

instance (GetTypes a, GetTypes b) => GetTypes (a,b) where
  getTypes (a',b') name = (i1++i2,s1++s2, (a,b))
    where (i1,s1,a) = getTypes a' (name ++ "a")
          (i2,s2,b) = getTypes b' (name ++ "b")

instance (GetTypes a, GetTypes b, GetTypes c) => GetTypes (a,b,c) where
  getTypes (a',b',c') name = (i1++i2++i3,s1++s2++s3, (a,b,c))
    where (i1,s1,a) = getTypes a' (name ++ "a")
          (i2,s2,b) = getTypes b' (name ++ "b")
          (i3,s3,c) = getTypes c' (name ++ "c")

instance (GetTypes a, GetTypes b, GetTypes c, GetTypes d) => GetTypes (a,b,c,d) where
  getTypes (a',b',c',d') name = (i1++i2++i3++i4,s1++s2++s3++s4, (a,b,c,d))
    where (i1,s1,a) = getTypes a' (name ++ "a")
          (i2,s2,b) = getTypes b' (name ++ "b")
          (i3,s3,c) = getTypes c' (name ++ "c")
          (i4,s4,d) = getTypes d' (name ++ "d")

instance ToProgram (Program a) where
  toProgram i prg () = ([], [], CG.compileStep1 prg)

instance (MemoryOps a, ASize l) => ToProgram (Push l a) where
  toProgram i a@(Push _ p) () = toProgram i prg ()
    where prg = do
            output <- outputArray a
            p (\a ix -> assignArray output a ix)

instance (GetTypes a, ToProgram b) => ToProgram (a -> b) where
  toProgram i f (a :- rest) = (ins ++ types, s1 ++ s2, prg)
    where (ins,s1,prg)   = toProgram (i+1) (f input) rest
          (types,s2,input) = getTypes a ("input" ++ show i)


---------------------------------------------------------------------------
-- heterogeneous lists of inputs 
---------------------------------------------------------------------------
data head :- tail = head :- tail

infixr 5 :-


---------------------------------------------------------------------------
-- Function types to input list types. 
---------------------------------------------------------------------------

type family InputList a

type instance InputList (a -> b)    = a :- (InputList b)
type instance InputList (Push l b)  = ()
type instance InputList (Program b) = () 

