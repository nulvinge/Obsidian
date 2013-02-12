{-# LANGUAGE MultiParamTypeClasses,  
             FlexibleInstances,
             ScopedTypeVariables,
             GADTs, 
             TypeFamilies #-}


import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Program
import Obsidian.Array
import Obsidian.Force

import Data.List
import Data.Word

data GArray = GArray
data BArray = BArray | BArrayG
data LArray = LArray | LArrayB | LArrayG

data Array d s a = Array [(d,s)] (s -> a)

type GArray1 a = Array GArray (Exp Word32) a
type BArray1 a = Array BArray (Exp Word32) a
type LArray1 a = Array LArray (Exp Word32) a


instance Indexible (Array d (Exp Word32)) a where
    access (Array _ _ f) = f



instance Len (Array d (Exp Word32)) where
    len (Array [(Literal n,_)] _) = n

--instance Resizeable (Array d (Exp Word32)) where
--    resize m (Array t _ f) = Array t (Literal m) f

instance (Scalar a) => Forceable (BArray1 (Exp a)) where
    type Forced (BArray1 (Exp a)) = BArray1 (Exp a)
    write_ (Array _ (Literal n) f) = do
        -- Allocate is a bit strange since
        -- it wants the n in bytes! But also knows the type. 
        name <- Allocate (n * fromIntegral (sizeOf (undefined :: Exp a)))
                            (Pointer (typeOf (undefined :: (Exp a))))

        ForAll (Just n) $ \i ->
            Assign name i (f i)
        return $ Array BArray (Literal n) (\i -> index name i)
    force p = do
        rval <- write_ p
        Sync
        return rval

class ReadArray t t2 a where
    readValue :: Array t (Exp Word32) a -> a
    readArray :: Array t (Exp Word32) a -> (Exp Word32) -> (Exp Word32) -> Array t2 (Exp Word32) a

instance (Scalar a) => ReadArray BArray LArray a where
    readValue (Array _ n f) = f (ThreadIdx X)
    readArray (Array _ n f) n2 bid = Array LArrayB n2 (\i -> f (n2*bid + i)) 

instance (Scalar a) => ReadArray GArray LArray a where
    readValue (Array _ n f) = f (BlockDim X * BlockIdx X + ThreadIdx X)
    readArray (Array _ n f) n2 bid = Array LArrayG n2 (\i -> f (n2*bid + i)) 

class WriteArray t1 t2 t3 a where
    writeArray :: Array t1 (Exp Word32) a -> Program t3 (Array t2 (Exp Word32) a)

instance (Scalar a) => WriteArray LArray BArray Block (Exp a) where
    writeArray (Array LArrayG n f) = return $ Array BArrayG n f
    writeArray (Array LArrayB n f) = return $ Array BArray n f
    writeArray (Array LArray (Literal n) f) = do
        let nt = Literal n
        let nb = BlockDim X
        let ns = nt `div` BlockDim X
        name <- Allocate (n * fromIntegral (sizeOf (undefined :: Exp a)))
                            (Pointer (typeOf (undefined :: (Exp a))))
        ForAll (Just n) $ \tid ->
            seqFor ns $ \sid -> do
                let bid = tid*ns + sid
                Assign name bid (f bid)
        Sync
        return $ Array BArray (Literal n) (\i -> index name i)

instance (Scalar a) => WriteArray LArray GArray Grid (Exp a) where
    writeArray (Array LArrayG n f) = return $ Array GArray n f
    writeArray (Array _ (Literal n) f) = do
        let nt = Literal n
        let nb = BlockDim X
        let ns = (nt `div` GridDim X) `div` BlockDim X
        name <- Output (typeOf (undefined :: Exp a))
        ForAllBlocks $ \bid ->
            ForAll Nothing $ \tid -> do
                seqFor ns $ \sid -> do
                    let gid = bid*nb + tid*ns + sid
                    Assign name gid (f gid)
        return $ Array GArray (Literal n) (\i -> index name i)

seqFor :: Exp Word32 -> (Exp Word32 -> Program Thread ()) -> Program Thread ()
seqFor (Literal 0) f = return ()
seqFor (Literal 1) f = f 0
seqFor n f           = SeqFor n f

class Uncharade t a where
    uncharade :: Array t s a -> Array t s a

instance Uncharade LArray a where
    uncharade (Array _ s a) = Array LArray s a

instance Uncharade BArray a where
    uncharade (Array _ s a) = Array BArray s a

instance Uncharade GArray a where
    uncharade (Array _ s a) = Array GArray s a

