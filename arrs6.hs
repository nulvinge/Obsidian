{-# LANGUAGE MultiParamTypeClasses,  
             FlexibleInstances,
             FlexibleContexts,
             UndecidableInstances,
             ScopedTypeVariables,
             RankNTypes
             #-}


import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Program
--import Obsidian.Array
--import Obsidian.Force

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.Program as CG
import Obsidian.CodeGen.InOut

import Prelude hiding (zipWith,sum,replicate)

import PExp

--import Data.List hiding (zipWith)
import Data.Word

data Pull d s a = Pull s (Exp Word32 -> a)

data Push d s a = Push s ((a -> Exp Word32 -> Program Thread ()) -> Program d ())


type GPull s a = Pull Grid   s a
type BPull s a = Pull Block  s a
type TPull s a = Pull Thread s a

type PullC d a = Pull d Word32        a
type PullP d a = Pull d (PExp Word32) a
type PullV d a = Pull d (Exp Word32)  a

type GPullA a = forall s. Pull s Grid   a
type BPullA a = forall s. Pull s Block  a
type TPullA a = forall s. Pull s Thread a

type APullC a = forall d. Pull Word32        d a
type APullP a = forall d. Pull (PExp Word32) d a
type APullV a = forall d. Pull (Exp Word32)  d a

type GPullC a = Pull Grid   Word32 a
type BPullC a = Pull Block  Word32 a
type TPullC a = Pull Thread Word32 a

type GPullP a = Pull Grid   (PExp Word32) a
type BPullP a = Pull Block  (PExp Word32) a
type TPullP a = Pull Thread (PExp Word32) a

type GPullV a = Pull Grid   (Exp Word32) a
type BPullV a = Pull Block  (Exp Word32) a
type TPullV a = Pull Thread (Exp Word32) a

type Pull2 d s a = Pull d s (Pull d s a)

type GPush s a = Push Grid   s a
type BPush s a = Push Block  s a
type TPush s a = Push Thread s a

type ID a = a

class (ToExp s) => Array a d s where
    amap :: (e -> e2) -> a d s e -> a d s e2
    len :: a d s e -> s
    resize :: s -> a d s e -> a d s e
    --force :: a d s e -> Program d (Pull d s e)

instance (Array a d s) => Functor (a d s) where
    fmap = amap

class Indexible a where
    access :: a d s e -> Exp Word32 -> e
    ixMap :: (Exp Word32 -> Exp Word32) -> a d s e -> a d s e

infixl 9 !
(!) :: Indexible a => a d s e -> Exp Word32 -> e
(!) = access

forAllP n f = ForAll (Just (toPExp n)) f

class Pushable a d where
    push :: (ToPExp s) => a d s e -> Push d s e

instance Pushable Pull Grid where
    push (Pull s ixf) =
        Push s $ \wf ->
        ForAllBlocks $ \bix -> do
            forAllP s $ \tix -> do
                let gix = (bix*BlockDim X + tix)
                wf (ixf gix) gix

instance Pushable Pull Block where
    push (Pull s ixf) =
        Push s $ \wf ->
            forAllP s $ \tix -> do
                wf (ixf tix) tix

{- allocate does not work yet
instance Pushable Pull Thread where
    push (Pull s ixf) =
        Push s $ \wf ->
            seqFor (toExp s) $ \six -> do
                wf (ixf six) six
-}

instance (ToExp s) => Array Pull d s where
    amap f (Pull s ixf) = Pull s (f.ixf)
    len (Pull n _) = n
    resize m (Pull _ f) = Pull m f

instance Indexible Pull where
    access (Pull _ f) = f
    ixMap f (Pull s ixf) = Pull s (ixf.f)

class (ToPExp s) => Forceable a d s where
    writeP :: (Scalar e) => a d s (Exp e) -> Program d (Pull d s (Exp e))
    forceP :: (Scalar e) => a d s (Exp e) -> Program d (Pull d s (Exp e))

force :: a d s e -> Program d (Pull d s e)
force = undefined

instance (Memory d s, SyncP d) => Forceable Push d s where
    writeP (Push s w :: Push d s (Exp e)) = do
        let t = (undefined :: Exp e)
        name <- allocateP (s * fromIntegral (sizeOf t))
                        (Pointer (typeOf t))
        w $ \e i -> Assign name i e
        return $ Pull s (\i -> index name i)
    forceP p = do
        r <- writeP p
        syncP
        return r

instance (Forceable Push d s, ToPExp s, Pushable Pull d) => Forceable Pull d s where
    writeP = writeP.push
    forceP = forceP.push

class (ToPExp s, SyncP d) => Memory d s where
    allocateP :: s -> Type -> Program d Name

instance (ToPExp s) => Memory Grid s where
    allocateP s t = Output t

instance Memory Block (PExp Word32) where
    allocateP n t = Allocate (unsafeFromPExp n) t

instance Memory Block Word32 where
    allocateP n t = Allocate n t

class SyncP d where
    syncP  :: Program d ()

instance SyncP Grid where
    syncP = return ()

instance SyncP Block where
    syncP = Sync

instance SyncP Thread where
    syncP = return ()

instance (Forceable Push d s) => Array Push d s where
    amap f (Push s wfi) = Push s $ \wf ->
        wfi (\a ix -> wf (f a) ix)
    len (Push s _) = s
    resize m (Push _ f) = Push m f

seqFor :: Exp Word32 -> (Exp Word32 -> Program Thread ()) -> Program Thread ()
seqFor (Literal 0) f = return ()
seqFor (Literal 1) f = f 0
seqFor n f           = SeqFor n f

mkPull2 :: s -> s -> (Exp Word32 -> Exp Word32 -> a) -> Pull2 d s a
mkPull2 s1 s2 f =
    Pull s1 $ \y ->
    Pull s2 $ \x ->
        f y x

segment :: (Array Pull d s) => s -> Pull d s e -> Pull d s (Pull d s e)
segment n (Pull s ixf) = 
    mkPull2 (s `div` n) n $ \y x ->
        ixf (y*(toExp n)+x)

divide :: (Array Pull d s) => s -> Pull d s e -> Pull d s (Pull d s e)
divide n (Pull s ixf) = 
    mkPull2 n (s `div` n) $ \y x ->
        ixf (y*(toExp (s `div` n))+x)


segment2 :: (Array Pull d s) => s -> s -> Pull2 d s a -> Pull2 d s (Pull2 d s a)
segment2 w h a =
    mkPull2 (s1 `div` w) (s2 `div` h) $ \xb yb ->
    mkPull2 w h $ \x y ->
        a ! (xb*(toExp w)+x) ! (yb*(toExp h)+y)
        where s1 = len a
              s2 = len (a!0) --hack

transf a x y = a ! y ! x

trans :: (Array Pull d s)
         => Pull2 d s a -> Pull2 d s a
trans a =
    mkPull2 s1 s2 $ \x y ->
        a ! y ! x
        where s1 = len a
              s2 = len (a!0) --hack


class (Array Pull d s) => Flatten d s e1 e where
    flatten :: Pull d s e1 -> Pull d s e

instance (Flatten d Word32 e (Exp e1)) => Flatten d Word32 (Pull d Word32 e) (Exp e1) where
    flatten a = Pull (len a*bl) f
        where bl = len ((flatten (a!0)) :: Pull d Word32 e)
              f ix = b ! (ix `div` (toExp bl))
                where b = flatten (a!(ix `div` (toExp (len b))))

--instance (Scalar e, Array Pull d (Exp Word32)) => Flatten d (Exp e) (Exp e) where
--    flatten = id

instance (Array Pull d s) => Flatten d s e e where
    flatten = id

trans1 :: (Array Pull d s, Flatten d s (Pull d s e) e)
       => s -> Pull d s e -> Pull d s e
trans1 w = flatten.trans.(segment w)

t1 :: (Flatten Grid s (Pull Grid s (Exp Int)) (Exp Int)) => s -> Pull Grid s (Exp Int) -> Pull Grid s (Exp Int)
t1 w = flatten.trans.(segment w)

t2 w = flatten.(trans).(segment w)

t3 w b = flatten.trans.(fmap (fmap trans)).(segment2 b b).(segment w)

mkT :: Pull d s e -> Pull Thread s e
mkT (Pull s f) = Pull s f

mkB :: Pull d s e -> Pull Block s e
mkB (Pull s f) = Pull s f

-- this is somewhat of a target
t4 w b = flatten.trans.(fmap (fmap (force.trans.mkB.(fmap mkB)))).(segment2 b b).(segment w)

-- to get the maximum performance, this is needed
diagonal = undefined
undiagonal = undefined
t5 w b = (ixMap diagonal).(t4 w b).(ixMap undiagonal)

transG :: (Array Pull Grid s) => Pull2 Grid s a -> Pull2 Grid s a
transG = trans

halve a = (a2 ! 0, a2 ! 1)
    where a2 = divide 2 a

zipWith :: (Array Pull d s) => (a -> b -> c) -> Pull d s a -> Pull d s b -> Pull d s c
zipWith op a1 a2 =
  Pull (min (len a1) (len a2))
       (\ix -> (a1 ! ix) `op` (a2 ! ix))

class (Pushable Pull d) => SForce d where
    sforce :: (Scalar e, Scalar e2)
           => (forall d2. (SForce d2) => Pull d2 Word32 (Exp e) -> Program d2 (Push d2 Word32 (Exp e2)))
           -> Pull d Word32 (Exp e) -> Program d (Push d Word32 (Exp e2))

forOneBlock f = ForAllBlocks $ \_ -> f  --wrong implementation

mapGPush :: (Pull Block Word32 e -> BProgram (Push Block Word32 t)) -> GPull Word32 e -> GPush Word32 t
mapGPush f a = Push (len a) $ \wf -> do --wrong len, should be s
            forOneBlock $ do
                Push s rf <- f (mkB a)
                rf wf

instance SForce Grid where
    sforce p a | len a <= 256 = return $ mapGPush f a
        where f b = do
                c <- forceP b
                p c
    --sforce p a = do
    --    b <- forceP a
    --    p b
        
        
instance SForce Block where
    {-
    sforce p a | len a <= 1 = do
        return $ Push 1 $ \wf ->
            ForAll (Just 1) $ \gix -> do
                b <- forceP (mkT a)
                Push s f <- p b
                f wf
    -}
    sforce p a | len a <= 32 = do
        b <- writeP a
        p b
    sforce p a = do
        b <- forceP a
        p b


mkGlobal n s = Pull s $ \gix -> index n gix

instance (Scalar t) => ToProgram (GPull s (Exp t)) (GProgram a) where
  toProgram i f (Pull s ixf) = ([(nom,Pointer t)],CG.runPrg (f input))
        where nom = "input" ++ show i
              input = mkGlobal nom s
              t = typeOf_ (undefined :: t)

instance (Scalar t, ToProgram b c) => ToProgram (GPull s (Exp t)) (b -> c) where
  toProgram i f ((Pull s ixf) :-> rest) = ((nom,Pointer t):ins,prg)
      where (ins,prg) = toProgram (i+1) (f input) rest
            nom = "input" ++ show i
            input = mkGlobal nom s
            t = typeOf_ (undefined :: t)

forceGP :: (ToPExp s, Scalar e)
        => (GPull s (Exp a) -> GProgram (GPush s (Exp e)))
        -> GPull s (Exp a) -> GProgram (GPull s (Exp e))
forceGP f = (>>= forceP).f

forceG :: (Forceable a Grid s, Scalar e) => a Grid s (Exp e) -> Program Grid (Pull Grid s (Exp e))
forceG = forceP

forceBP f = forOneBlock f

quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

testInput :: GPullC (Exp Int)
testInput = mkGlobal "apa" 256

--testPrint :: (ToProgram a b, Ips a b ~ Pull Grid (Exp Int)) => (a -> b) -> IO ()
--testPrint f = quickPrint f testInput

rh0 :: (Memory d Word32, Pushable Pull d, Scalar e, Num (Exp e)) => Pull d Word32 (Exp e) -> Program d (Push d Word32 (Exp e))
rh0 a | len a == 1 = return $ push a
rh0 a = ((>>= rh0).forceP.uncurry (zipWith (+)).halve) a

trh0 :: IO ()
trh0 = quickPrint (forceP.mapGPush rh0) testInput

rh1 :: (SForce d, Scalar e, Num (Exp e)) => Pull d Word32 (Exp e) -> Program d (Push d Word32 (Exp e))
rh1 a | len a == 1 = return $ push a
rh1 a = (sforce rh1.uncurry (zipWith (+)).halve) a

trh1 :: IO ()
trh1 = quickPrint (forceGP rh1) testInput

rh2 :: (SForce d, Scalar e, Num (Exp e)) => Pull d Word32 (Exp e) -> Program d (Push d Word32 (Exp e))
rh2 a | len a == 2 = (return.push.uncurry (zipWith (+)).halve) a
rh2 a = (sforce rh2.uncurry (zipWith (+)).halve) a

trh2 :: IO ()
trh2 = quickPrint (forceGP rh2) testInput

rh3 :: (SForce d, Scalar e, Num (Exp e)) => Pull d Word32 (Exp e) -> Program d (Push d Word32 (Exp e))
rh3 a | len a == 1 = return $ push a
rh3 a = (rh3.uncurry (zipWith (+)).halve) `sforce` a

trh3 :: IO ()
trh3 = quickPrint (forceGP rh3) testInput

rh4 :: (SForce d, Scalar e, Num (Exp e)) => Pull d Word32 (Exp e) -> Program d (Push d Word32 (Exp e))
rh4 a | (len a) == 1 = return $ push a
rh4 a = (rh4.uncurry (zipWith (+)).halve) `sforce` a
rh4' = (rh4.uncurry (zipWith (+)).halve)

trh4 :: IO ()
trh4 = quickPrint (forceGP rh4') testInput

