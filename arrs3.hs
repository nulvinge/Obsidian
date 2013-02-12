{-# LANGUAGE MultiParamTypeClasses,  
             FlexibleInstances,
             FlexibleContexts,
             UndecidableInstances,
             ScopedTypeVariables,
             GADTs, 
             TypeFamilies #-}


import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Program
--import Obsidian.Array
--import Obsidian.Force

import Data.List
import Data.Word

data Pull d s a = Pull d s (s -> a)

type GPull a = Pull Grid   (Exp Word32) a
type BPull a = Pull Block  (Exp Word32) a
type TPull a = Pull Thread (Exp Word32) a

type Pull2 d a = Pull d (Exp Word32) (Pull d (Exp Word32) a)

data Push d s a = Push d s ((a -> s -> Program Thread ()) -> Program d ())

type GPush a = Push Grid   (Exp Word32) a
type BPush a = Push Block  (Exp Word32) a
type TPush a = Push Thread (Exp Word32) a

class Array a d s where
    amap :: (e -> e2) -> a d s e -> a d s e2
    len :: a d s e -> s
    resize :: s -> a d s e -> a d s e
    --force :: a d s e -> Program d (Pull d s e)

instance (Array a d s) => Functor (a d s) where
    fmap = amap

class Indexible a where
    access :: a d s e -> s -> e
    ixMap :: (s -> s) -> a d s e -> a d s e

infixl 9 !
(!) :: Indexible a => a d s e -> s -> e
(!) = access

class Pushable a d s where
    push :: a d s e -> Push d s e

instance Pushable Pull Grid (Exp Word32) where
    push (Pull d s ixf) =
        Push d s $ \wf ->
        ForAllBlocks $ \bix -> do
            let (Literal nb) = s `div` GridDim X
            ForAll (Just nb) $ \tix -> do
                let gix = (bix*(Literal nb) + tix)
                wf (ixf gix) gix


instance Pushable Pull Block (Exp Word32) where
    push (Pull d (Literal s) ixf) =
        Push d (Literal s) $ \wf ->
            ForAll (Just s) $ \tix -> do
                wf (ixf tix) tix

instance (Forceable Push d s e, Pushable Pull d s) => Array Pull d s where
    amap f (Pull d s ixf) = Pull d s (f.ixf)
    len (Pull _ n _) = n
    resize m (Pull t _ f) = Pull t m f

instance Indexible Pull where
    access (Pull _ _ f) = f
    ixMap f (Pull d s ixf) = Pull d s (ixf.f)

class Forceable a d s e where
    writeP :: a d s (Exp e) -> Program d (Pull d s (Exp e))
    forceP :: a d s (Exp e) -> Program d (Pull d s (Exp e))

instance (Memory d, Scalar e) => Forceable Push d (Exp Word32) e where
    writeP (Push d s w) = do
        name <- allocateP (s * fromIntegral (sizeOf (undefined :: Exp e)))
                          (Pointer (typeOf (undefined :: (Exp e))))
        w (targetArr name)
        -- BSync
        return $ Pull d s (\i -> index name i)
        where
            targetArr name e i = Assign name i e
    forceP p = do
        r <- writeP p
        syncP
        return r

instance (Forceable Push d s e, Pushable Pull d s) => Forceable Pull d s e where
    writeP = writeP.push
    forceP = forceP.push

class Memory d where
    syncP  :: Program d ()
    allocateP :: Exp Word32 -> Type -> Program d Name

instance Memory Grid where
    syncP = return ()
    allocateP s t = Output t

instance Memory Block where
    syncP = Sync
    allocateP (Literal n) t = Allocate n t

instance Memory Thread where
    syncP = return ()
    allocateP s t = undefined

instance (Forceable Push d s e) => Array Push d s where
    amap f (Push d s wfi) = Push d s $ \wf ->
        wfi (\a ix -> wf (f a) ix)
    len (Push _ s _) = s
    resize m (Push d _ f) = Push d m f

seqFor :: Exp Word32 -> (Exp Word32 -> Program Thread ()) -> Program Thread ()
seqFor (Literal 0) f = return ()
seqFor (Literal 1) f = f 0
seqFor n f           = SeqFor n f

mkPull2 d s1 s2 f =
    Pull d s1 $ \x ->
    Pull d s2 $ \y ->
        f x y

segment :: (Integral s) => s -> Pull d s e -> Pull d s (Pull d s e)
segment n (Pull d s ixf) = 
    mkPull2 d (s `div` n) n $ \x y ->
        ixf (y*n+x)


segment2 :: (Array Pull d (Exp Word32))
         => (Exp Word32) -> (Exp Word32) -> d -> Pull2 d a
         -> Pull2 d (Pull2 d a)
segment2 w h d a =
    mkPull2 d (s1 `div` w) (s2 `div` h) $ \xb yb ->
    mkPull2 d w h $ \x y ->
        a ! (xb*w+x) ! (yb*h+y)
        where s1 = len a
              s2 = len (a!0) --hack

transf a x y = a ! y ! x

trans :: (Array Pull d (Exp Word32))
         => d -> Pull2 d a -> Pull2 d a
trans d a =
    mkPull2 d s1 s2 $ \x y ->
        a ! y ! x
        where s1 = len a
              s2 = len (a!0) --hack

class (Array Pull d (Exp Word32)) => Flatten d e1 e where
    flatten :: Pull d (Exp Word32) e1 -> Pull d (Exp Word32) e

instance (Flatten d e (Exp e1)) => Flatten d (Pull d (Exp Word32) e) (Exp e1) where
    flatten a@(Pull d _ _) = Pull d (len a*bl) f
        where bl = len ((flatten (a!0)) :: Pull d (Exp Word32) e)
              f ix = b ! (ix `div` (len b))
                where b = flatten (a!(ix `div` len b))

--instance (Scalar e, Array Pull d (Exp Word32)) => Flatten d (Exp e) (Exp e) where
--    flatten = id

instance (Array Pull d (Exp Word32)) => Flatten d e e where
    flatten = id

trans1 :: (Array Pull d (Exp Word32), Flatten d (Pull d (Exp Word32) e) e)
       => Exp Word32 -> d -> Pull d (Exp Word32) e -> Pull d (Exp Word32) e
trans1 w d = flatten.trans d.(segment w)


--t1 :: Exp Word32 -> Grid -> Pull Grid (Exp Word32) (Exp Int) -> Pull Grid (Exp Word32) (Exp Int)
--t1 = trans1

class Level d where
    mkLevel :: d

instance Level Grid where
    mkLevel = undefined
instance Level Block where
    mkLevel = undefined
--instance Level Thread where
--    mkLevel = const 0
