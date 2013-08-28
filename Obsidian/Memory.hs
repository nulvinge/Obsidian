{-# LANGUAGE ScopedTypeVariables,
             TypeFamilies,
             GADTs #-}

{- Joel Svensson 2013

   This Module became quite messy.
   TODO: CLEAN IT UP! 

   notes: 2013-05-02: Cleaned out inspect. 

-} 

module Obsidian.Memory (MemoryOps(..), Names,
  typesScalar, typesArray, getNames,
  allocateScalar, allocateArray, outputArray,
  names, inNames, valType, atomicArray,
  forceScalar, scalarForce
  )  where


import Obsidian.Program
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Types
import Obsidian.Array -- Importing this feels a bit strange. 
import Obsidian.Atomic

import Data.Word

data Names = Single Name Type Int
           | Tuple [Names]
  deriving (Show,Eq)

inNames :: Name -> Names -> Bool
inNames n (Single name _ _) = n == name
inNames n (Tuple names) = any (inNames n) names

---------------------------------------------------------------------------
-- Local Memory
---------------------------------------------------------------------------
class MemoryOps a where
  createNames    :: a -> Name -> Names
  assignArray    :: Names -> a -> Exp Word32 -> Program ()
  assignScalar   :: Names -> a -> Program () 
  pullFrom       :: (ASize s) => Names -> s -> Pull s a
  readFrom       :: Names -> a


---------------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------------
instance Scalar a => MemoryOps (Exp a) where
  createNames a n = Single n (typeOf a) (sizeOf a)
  assignArray  (Single name t s) a ix   = Assign name [ix] a
  assignScalar (Single name t s) a      = Assign name [] a  
  pullFrom (Single name t s) n = Pull n (\i -> index name i) 
  readFrom (Single name t s) = variable name


instance (MemoryOps a, MemoryOps b) => MemoryOps (a, b) where
  createNames _ n = Tuple [createNames (undefined :: a) (n++"a")
                          ,createNames (undefined :: b) (n++"b")]
  assignArray (Tuple [ns1,ns2]) (a,b) ix = do
    assignArray ns1 a ix 
    assignArray ns2 b ix 
  assignScalar (Tuple [ns1,ns2]) (a,b) = do
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

{-
instance (Scalar a) => MemoryOps (Exp a,Exp a) where
  createNames (a,b) n = Single n (VectorT 2 (typeOf a)) (2*sizeOf a)
  assignArray  (Single name t s) (a,b) ix   = do
    Assign (name++"a") [ix] a
    Assign (name++"b") [ix] b
  assignScalar (Single name t s) (a,b)  = do
    Assign (name++".x") [] a
    Assign (name++".y") [] a
  pullFrom (Single name t s) n =
    let p1 = Pull n (\i -> index name i) 
        p2 = Pull n (\i -> index name i) 
    in Pull n (\ix -> (p1 ! ix, p2 ! ix))
  readFrom (Single name t s) = (variable $ name++".x",variable $ name++".y")
-}

instance (MemoryOps a, MemoryOps b, MemoryOps c) => MemoryOps (a, b, c) where
  createNames _ n = Tuple [createNames (undefined :: a) (n++"a")
                          ,createNames (undefined :: b) (n++"b")
                          ,createNames (undefined :: c) (n++"c")]
  assignArray (Tuple [ns1,ns2,ns3]) (a,b,c) ix = do
    assignArray ns1 a ix 
    assignArray ns2 b ix 
    assignArray ns3 c ix 
  assignScalar (Tuple [ns1,ns2,ns3]) (a,b,c) = do
    assignScalar ns1 a
    assignScalar ns2 b 
    assignScalar ns3 c 
  pullFrom (Tuple [ns1,ns2,ns3]) n =
    let p1 = pullFrom ns1 n
        p2 = pullFrom ns2 n
        p3 = pullFrom ns3 n
    in Pull n (\ix -> (p1 ! ix, p2 ! ix, p3 ! ix))
  readFrom (Tuple [ns1,ns2,ns3])  =
    let p1 = readFrom ns1
        p2 = readFrom ns2
        p3 = readFrom ns3
    in (p1,p2,p3)

instance (MemoryOps a, MemoryOps b, MemoryOps c, MemoryOps d) => MemoryOps (a, b, c, d) where
  createNames _ n = Tuple [createNames (undefined :: a) (n++"a")
                          ,createNames (undefined :: b) (n++"b")
                          ,createNames (undefined :: c) (n++"c")
                          ,createNames (undefined :: d) (n++"d")]
  assignArray (Tuple [ns1,ns2,ns3,ns4]) (a,b,c,d) ix = do
    assignArray ns1 a ix 
    assignArray ns2 b ix 
    assignArray ns3 c ix 
    assignArray ns4 d ix 
  assignScalar (Tuple [ns1,ns2,ns3,ns4]) (a,b,c,d) = do
    assignScalar ns1 a
    assignScalar ns2 b 
    assignScalar ns3 c 
    assignScalar ns4 d 
  pullFrom (Tuple [ns1,ns2,ns3,ns4]) n =
    let p1 = pullFrom ns1 n
        p2 = pullFrom ns2 n
        p3 = pullFrom ns3 n
        p4 = pullFrom ns4 n
    in Pull n (\ix -> (p1 ! ix, p2 ! ix, p3 ! ix, p4 ! ix))
  readFrom (Tuple [ns1,ns2,ns3,ns4])  =
    let p1 = readFrom ns1
        p2 = readFrom ns2
        p3 = readFrom ns3
        p4 = readFrom ns4
    in (p1,p2,p3,p4)


atomicArray  (Single name t s) ix f = AtomicOp name ix f --what about a?

valType :: a b m -> m
valType = (undefined :: m)

names :: (MemoryOps a) => a -> Program Names 
names a = do
  n <- uniqueSM
  return $ createNames a n

typesScalar :: Names -> [(Name,Type)]
typesScalar (Single n t s) = [(n,t)]
typesScalar (Tuple ns) = concat $ map typesScalar ns

getNames :: Names -> [Name]
getNames (Single n _ _) = [n]
getNames (Tuple ns) = concat $ map getNames ns

typesArray ns = map (\(n,t) -> (n, Pointer t))
                    (typesScalar ns)

allocateScalar :: Names -> Program () 
allocateScalar (Single name t s) =
  Declare name t
allocateScalar (Tuple ns) =
  mapM_ (allocateScalar) ns

allocateArray  :: Names -> Word32 -> Program ()
allocateArray (Single name t s) n = 
  Allocate name (n * fromIntegral s) (Pointer t)
allocateArray (Tuple ns) n =
  mapM_ (\a -> allocateArray a n) ns

outputArray :: (MemoryOps a, ASize s, Array p) => p s a -> Program Names
outputArray a = do
  let ns = createNames (valType a) "dummyOutput"
  outputArray' (sizeConv $ len a) ns
outputArray' l (Single name t s) = do
  name' <- Output (Pointer t) l
  return $ Single name' t s
outputArray' l (Tuple ns) = do
  ns' <- mapM (outputArray' l) ns
  return $ Tuple ns'

forceScalar :: (MemoryOps a) => Name -> a -> Program a
forceScalar name a = do
  let names = createNames a name
  allocateScalar names
  assignScalar names a
  return $ readFrom names

scalarForce a = do
  n <- uniqueSM
  forceScalar n a
  

