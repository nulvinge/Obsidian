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
  toProgram :: Int -> (a -> b) -> Ips a b -> (Inputs,CG.Program ())

typeOf_ a = typeOf (Literal a)

class Vector a where
  getTypes :: a -> Name -> (a,[(Name,Type)])

instance (Scalar a) => Vector (Exp a) where
  getTypes a n = (variable n,[(n, typeOf a)])

instance (Scalar a) => Vector (GlobPull (Exp a)) where
  getTypes a n = (namedGlobal n,[(n, Pointer (typeOf_ (undefined :: a)))])

instance (Scalar a, Scalar b) => Vector (Exp a, Exp b) where
  getTypes (a,b) n = ((aa,ba),at++bt)
    where (aa,at) = getTypes a (n++"a")
          (ba,bt) = getTypes b (n++"b")

zipG :: GlobPull a -> GlobPull b -> GlobPull (a, b)
zipG arr1 arr2 = GlobPull $ \ix -> (arr1 ! ix, arr2 ! ix)

instance (Scalar a, Scalar b) => Vector (GlobPull (Exp a, Exp b)) where
  getTypes _ n = (zipG aa ba,at++bt)
    where (aa,at) = getTypes (undefined :: GlobPull (Exp a)) (n++"a")
          (ba,bt) = getTypes (undefined :: GlobPull (Exp b)) (n++"b")

instance (Vector a) => ToProgram a (GProgram b) where
  toProgram i f a = (types, CG.runPrg (f input))
    where (input,types) = getTypes (undefined :: a) ("input" ++ show i)

instance (Vector a) => ToProgram a (Final (GProgram b)) where
  toProgram i f a = (types, CG.runPrg (cheat (f input)))
    where (input,types) = getTypes (undefined :: a) ("input" ++ show i)

instance (Vector a, ToProgram b c) => ToProgram a (b -> c) where
  toProgram i f (a :-> rest) = (ins ++ types,prg)
    where (ins,prg) = toProgram (i+1) (f input) rest
          (input,types) = getTypes (undefined :: a) ("input" ++ show i)

{-
instance (Scalar t) => ToProgram (Exp t) (GProgram b) where
  toProgram i f a = ([(nom,t)],CG.runPrg (f input))
    where nom = "s" ++ show i
          input = variable nom
          t = typeOf_ (undefined :: t)

instance (Scalar t) => ToProgram (GlobPull (Exp t)) (GProgram a) where
  toProgram i f (GlobPull ixf) = ([(nom,Pointer t)],CG.runPrg (f input)) 
      where nom = "input" ++ show i 
            input = namedGlobal nom
            t = typeOf_ (undefined :: t)

instance (Scalar t) => ToProgram (GlobPull (Exp t)) (Final (GProgram a)) where
  toProgram i f (GlobPull ixf) = ([(nom,Pointer t)],CG.runPrg (cheat (f input))) 
      where nom = "input" ++ show i 
            input = namedGlobal nom
            t = typeOf_ (undefined :: t)

instance (Scalar t, ToProgram b c) => ToProgram (Exp t) (b -> c) where
  toProgram i f (a :-> rest) = ((nom,t):ins,prg)
    where
      (ins,prg) = toProgram (i+1) (f input) rest
      nom = "s" ++ show i
      input = variable nom
      t = typeOf_ (undefined :: t)

instance (Scalar t, ToProgram b c) => ToProgram (GlobPull (Exp t)) (b -> c) where
  toProgram i f ((GlobPull ixf) :-> rest) = ((nom,Pointer t):ins,prg)
    where
      (ins,prg) = toProgram (i+1) (f input) rest
      nom = "input" ++ show i
      input = namedGlobal nom
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
type instance Ips a (Final (GProgram b)) = a 
type instance Ips a (GProgram b) = a
type instance Ips a (b -> c) =  a :-> Ips b c

{- TODO:
    What about Distrib (Array p1 a1, Array p2 a2)
     (blocks of pairs of arrays) -- limit what can live inside a block  ? 


-} 

