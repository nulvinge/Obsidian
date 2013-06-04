{-# LANGUAGE FlexibleInstances, 
             FlexibleContexts,
             MultiParamTypeClasses,
             TypeOperators,
             TypeFamilies ,
             ScopedTypeVariables
             #-}

{- Joel Svensson 2012, 2013
   Niklas Ulvinge 2013

  Notes:

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
import Obsidian.Memory
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

class ToProgram a b where
  toProgram :: Int -> (a -> b) -> Ips a b -> (Inputs,CG.IM)

class GetTypes a where
  getTypes :: a -> Name -> (Inputs,a)

instance (MemoryOps a) => GetTypes (Pull Word32 a) where
  getTypes a name = (typesArray names
                    ,pullFrom names (len a))
      where names = createNames (valType a) name

instance (MemoryOps a) => GetTypes (Pull (Exp Word32) a) where
  getTypes a name = ((namen, Word32) : typesArray names
                    ,pullFrom names (variable namen))
      where namen = name ++ "n"
            names = createNames (valType a) name

instance (Scalar a) => GetTypes (Exp a) where
  getTypes a name = (typesScalar names
                    ,readFrom names)
      where namen = name ++ "n"
            names = createNames a name

instance (GetTypes a, GetTypes b) => GetTypes (a,b) where
  getTypes a name = (i1++i2, (a,b))
    where (i1,a) = getTypes a (name ++ "a")
          (i2,b) = getTypes b (name ++ "b")

instance (GetTypes a) => ToProgram a (GProgram b) where
  toProgram i f a = (types, CG.compileStep1 (f input))
    where (types,input) = getTypes a ("input" ++ show i)

instance (GetTypes a, ToProgram b c) => ToProgram a (b -> c) where
  toProgram i f (a :-> rest) = (ins ++ types, prg)
    where (ins,prg)     = toProgram (i+1) (f input) rest
          (types,input) = getTypes a ("input" ++ show i)



---------------------------------------------------------------------------
-- heterogeneous lists of inputs 
---------------------------------------------------------------------------
data head :-> tail = head :-> tail

infixr 5 :->


---------------------------------------------------------------------------
-- Function types to input list types. 
--------------------------------------------------------------------------- 
type family Ips a b
 
-- type instance Ips a (GlobArray b) = Ips' a -- added Now 26
-- type instance Ips a (Final (GProgram b)) = a 
type instance Ips a (GProgram b) = a
type instance Ips a (b -> c) =  a :-> Ips b c


