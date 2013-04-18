{-# LANGUAGE ScopedTypeVariables  #-}


{- Joel Svensson 2013 -} 

module Obsidian.Memory (MemoryOps(..), Names, names, typesArray, inNames)  where


import Obsidian.Program
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Types
import Obsidian.Array -- Importing this feels a bit strange. 

import Data.Word

data Names = Single Name
           | Tuple [Names]
  deriving (Show,Eq)

inNames :: Name -> Names -> Bool
inNames n (Single name) = n == name
inNames n (Tuple names) = any (inNames n) names

class MemoryOps a where
  createNames    :: a -> Name -> Names
  typesScalar    :: Names -> a -> [(Name,Type)]
  allocateArray  :: Names -> a -> Word32 -> Program t ()
  allocateScalar :: Names -> a -> Program t () 
  assignArray    :: Names -> a -> Exp Word32 -> TProgram ()
  assignScalar   :: Names -> a -> TProgram () 
  pullFrom       :: (ASize s) => Names -> s -> Pull s a
  readFrom       :: Names -> a


names :: (MemoryOps a) => a -> Program t Names 
names a = do
  n <- uniqueSM
  return $ createNames a n

typesArray ns a = map (\(n,t) -> (n,Pointer t)) (typesScalar ns a)

instance Scalar a => MemoryOps (Exp a) where
  createNames a n = Single n
  typesScalar (Single n) a = [(n, typeOf a)]
  allocateArray (Single name) a n = 
    Allocate name (n * fromIntegral (sizeOf a))
                  (Pointer (typeOf a))
  allocateScalar (Single name) a =
    Declare name (typeOf a) 
  assignArray  (Single name) a ix = Assign name [ix] a
  assignScalar (Single name) a    = Assign name [] a  
  pullFrom (Single name) n = Pull n (\i -> index name i) 
  readFrom (Single name) = variable name

instance (MemoryOps a, MemoryOps b) => MemoryOps (a, b) where
  createNames _ n = Tuple [createNames (undefined :: a) (n++"a")
                          ,createNames (undefined :: b) (n++"b")]
  typesScalar (Tuple [na,nb]) _ = typesScalar na (undefined :: a)
                               ++ typesScalar nb (undefined :: b)
  allocateArray (Tuple [ns1,ns2]) _ n =
    do 
      allocateArray ns1 (undefined :: a) n
      allocateArray ns2 (undefined :: b) n
  allocateScalar (Tuple [ns1,ns2]) _ =
    do
      allocateScalar ns1 (undefined :: a)
      allocateScalar ns2 (undefined :: b) 
  assignArray (Tuple [ns1,ns2]) (a,b) ix =
    do
      assignArray ns1 a ix 
      assignArray ns2 b ix 
  assignScalar (Tuple [ns1,ns2]) (a,b) =
    do
      assignScalar ns1 a
      assignScalar ns2 b 
  pullFrom (Tuple [ns1,ns2]) n =
    let p1 = pullFrom ns1 n
        p2 = pullFrom ns2 n
    in Pull n (\ix -> (p1 ! ix, p2 ! ix))
  readFrom (Tuple [ns1,ns2])  =
    let p1 = readFrom ns1
        p2 = readFrom ns2
    in (p1,p2) 

