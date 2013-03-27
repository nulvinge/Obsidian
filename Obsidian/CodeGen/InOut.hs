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
  
typeOf_ a = typeOf (Literal a)

class Vector a where
  getTypes :: a -> Name -> (a,[(Name,Type)])

instance (Scalar a) => Vector (Exp a) where
  getTypes a n = (variable n,[(n, typeOf a)])

instance (Scalar a) => Vector (Pull (Exp Word32) (Exp a)) where
  getTypes a n = (input,[(n, Pointer (typeOf_ (undefined :: a))), (nn,Word32)])
    where nn        = n ++ "n"
          input = namedGlobal n (variable n)

instance (Scalar a, Scalar b) => Vector (Exp a, Exp b) where
  getTypes (a,b) n = ((aa,ba),at++bt)
    where (aa,at) = getTypes a (n++"a")
          (ba,bt) = getTypes b (n++"b")

zipG :: Pull (Exp Word32) a -> Pull (Exp Word32) b -> Pull (Exp Word32) (a, b)
zipG arr1 arr2 = Pull (min (len arr1) (len arr2)) $ \ix -> (arr1 ! ix, arr2 ! ix)

instance (Scalar a, Scalar b) => Vector (Pull (Exp Word32) (Exp a, Exp b)) where
  getTypes _ n = (zipG aa ba,at++bt)
    where (aa,at) = getTypes (undefined :: Pull (Exp Word32) (Exp a)) (n++"a")
          (ba,bt) = getTypes (undefined :: Pull (Exp Word32) (Exp b)) (n++"b")

instance (Vector a) => ToProgram a (GProgram b) where
  toProgram i f a = (types, CG.compileStep1 (f input))
    where (input,types) = getTypes (undefined :: a) ("input" ++ show i)

--instance (Vector a) => ToProgram a (Final (GProgram b)) where
--  toProgram i f a = (types, CG.compileStep1 (cheat (f input)))
--    where (input,types) = getTypes (undefined :: a) ("input" ++ show i)

instance (Vector a, ToProgram b c) => ToProgram a (b -> c) where
  toProgram i f (a :-> rest) = (ins ++ types,prg)
    where (ins,prg) = toProgram (i+1) (f input) rest
          (input,types) = getTypes (undefined :: a) ("input" ++ show i)

{-
instance (Scalar t) => ToProgram (Exp t) (GProgram b) where
  toProgram i f a = ([(nom,t)],CG.compileStep1 (f input))
    where nom = "s" ++ show i
          input = variable nom
          t = typeOf_ (undefined :: t)


-- UPDATE THIS: The rest of the code gen will need a length variable
instance (Scalar t) => ToProgram (Pull (Exp Word32) (Exp t)) (GProgram a) where
  toProgram i f (Pull n ixf) = ([(nom,Pointer t),(n,Word32)],CG.compileStep1 (f input)) 
      where nom = "input" ++ show i
            n   = "n" ++ show i 
            lengthVar = variable n
            input = namedGlobal nom lengthVar
            t = typeOf_ (undefined :: t)


instance (Scalar t, ToProgram b c) => ToProgram (Exp t) (b -> c) where
  toProgram i f (a :-> rest) = ((nom,t):ins,prg)
    where
      (ins,prg) = toProgram (i+1) (f input) rest
      nom = "s" ++ show i
      input = variable nom
      t = typeOf_ (undefined :: t)


instance (Scalar t, ToProgram b c) => ToProgram (Pull (Exp Word32) (Exp t)) (b -> c) where
  toProgram i f ((Pull n ixf) :-> rest) = ((nom,Pointer t):(n,Word32):ins,prg)
    where
      (ins,prg) = toProgram (i+1) (f input) rest
      nom = "input" ++ show i
      n   = "n" ++ show i
      lengthVar = variable n
      input = namedGlobal nom lengthVar
      t = typeOf_ (undefined :: t)
-}


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


