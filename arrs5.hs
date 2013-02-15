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

--import Data.List hiding (zipWith)
import Data.Word

data Pull d a = Pull Word32 (Exp Word32 -> a)

data Push d a = Push Word32 ((a -> Exp Word32 -> Program Thread ()) -> Program d ())

type GPull a = Pull Grid   a
type BPull a = Pull Block  a
type TPull a = Pull Thread a

type Pull2 d a = Pull d (Pull d a)

type GPush a = Push Grid   a
type BPush a = Push Block  a
type TPush a = Push Thread a

class Array a d where
    amap :: (e -> e2) -> a d e -> a d e2
    len :: a d e -> Word32
    resize :: Word32 -> a d e -> a d e
    --force :: a d s e -> Program d (Pull d s e)

instance (Array a d) => Functor (a d) where
    fmap = amap

class Indexible a where
    access :: a d e -> Exp Word32 -> e
    ixMap :: (Exp Word32 -> Exp Word32) -> a d e -> a d e

infixl 9 !
(!) :: Indexible a => a d e -> Exp Word32 -> e
(!) = access

class Pushable a d where
    push :: a d e -> Push d e

instance Pushable Pull Grid where
    push (Pull s ixf) =
        Push s $ \wf ->
        ForAllBlocks $ \bix -> do
            ForAll Nothing $ \tix -> do
                let gix = (bix*BlockDim X + tix)
                Cond (gix <* (Literal s)) $ wf (ixf gix) gix


instance Pushable Pull Block where
    push (Pull s ixf) =
        Push s $ \wf ->
            ForAll (Just s) $ \tix -> do
                wf (ixf tix) tix

{- allocate does not work yet
instance Pushable Pull Thread where
    push (Pull s ixf) =
        Push s $ \wf ->
            seqFor (Literal s) $ \six -> do
                wf (ixf six) six
-}

instance Array Pull d where
    amap f (Pull s ixf) = Pull s (f.ixf)
    len (Pull n _) = n
    resize m (Pull _ f) = Pull m f

instance Indexible Pull where
    access (Pull _ f) = f
    ixMap f (Pull s ixf) = Pull s (ixf.f)

class Forceable a d e where
    writeP :: a d (Exp e) -> Program d (Pull d (Exp e))
    forceP :: a d (Exp e) -> Program d (Pull d (Exp e))

force :: a d e -> Program d (Pull d e)
force = undefined

instance (Memory d, Scalar e) => Forceable Push d e where
    writeP (Push s w) = do
        name <- allocateP (s * fromIntegral (sizeOf (undefined :: Exp e)))
                          (Pointer (typeOf (undefined :: (Exp e))))
        w $ \e i -> Assign name i e
        return $ Pull s (\i -> index name i)
    forceP p = do
        r <- writeP p
        syncP
        return r

instance (Forceable Push d e, Pushable Pull d) => Forceable Pull d e where
    writeP = writeP.push
    forceP = forceP.push

class Memory d where
    syncP  :: Program d ()
    allocateP :: Word32 -> Type -> Program d Name

instance Memory Grid where
    syncP = return ()
    allocateP s t = Output t

instance Memory Block where
    syncP = Sync
    allocateP n t = Allocate n t

instance Memory Thread where
    syncP = return ()
    allocateP s t = undefined

instance (Forceable Push d e) => Array Push d where
    amap f (Push s wfi) = Push s $ \wf ->
        wfi (\a ix -> wf (f a) ix)
    len (Push s _) = s
    resize m (Push _ f) = Push m f

seqFor :: Exp Word32 -> (Exp Word32 -> Program Thread ()) -> Program Thread ()
seqFor (Literal 0) f = return ()
seqFor (Literal 1) f = f 0
seqFor n f           = SeqFor n f

mkPull2 :: Word32 -> Word32 -> (Exp Word32 -> Exp Word32 -> a) -> Pull2 d a
mkPull2 s1 s2 f =
    Pull s1 $ \y ->
    Pull s2 $ \x ->
        f y x

segment :: Word32 -> Pull d e -> Pull d (Pull d e)
segment n (Pull s ixf) = 
    mkPull2 (s `div` n) n $ \y x ->
        ixf (y*(Literal n)+x)

divide :: Word32 -> Pull d e -> Pull d (Pull d e)
divide n (Pull s ixf) = 
    mkPull2 n (s `div` n) $ \y x ->
        ixf (y*((Literal s) `div` (Literal n))+x)


segment2 :: (Array Pull d) => Word32 -> Word32 -> Pull2 d a -> Pull2 d (Pull2 d a)
segment2 w h a =
    mkPull2 (s1 `div` w) (s2 `div` h) $ \xb yb ->
    mkPull2 w h $ \x y ->
        a ! (xb*(Literal w)+x) ! (yb*(Literal h)+y)
        where s1 = len a
              s2 = len (a!0) --hack

transf a x y = a ! y ! x

trans :: (Array Pull d)
         => Pull2 d a -> Pull2 d a
trans a =
    mkPull2 s1 s2 $ \x y ->
        a ! y ! x
        where s1 = len a
              s2 = len (a!0) --hack


class (Array Pull d) => Flatten d e1 e where
    flatten :: Pull d e1 -> Pull d e

instance (Flatten d e (Exp e1)) => Flatten d (Pull d e) (Exp e1) where
    flatten a = Pull (len a*bl) f
        where bl = len ((flatten (a!0)) :: Pull d e)
              f ix = b ! (ix `div` (Literal (len b)))
                where b = flatten (a!(ix `div` (Literal (len b))))

--instance (Scalar e, Array Pull d (Exp Word32)) => Flatten d (Exp e) (Exp e) where
--    flatten = id

instance (Array Pull d) => Flatten d e e where
    flatten = id

trans1 :: (Array Pull d, Flatten d (Pull d e) e)
       => Word32 -> Pull d e -> Pull d e
trans1 w = flatten.trans.(segment w)

t1 :: Word32 -> Pull Grid (Exp Int) -> Pull Grid (Exp Int)
t1  w = flatten.trans.(segment w)

t2 w = flatten.(trans).(segment w)

t3 w b = flatten.trans.(fmap (fmap trans)).(segment2 b b).(segment w)

mkT :: Pull d e -> Pull Thread e
mkT (Pull s f) = Pull s f

mkB :: Pull d e -> Pull Block e
mkB (Pull s f) = Pull s f

-- this is somewhat of a target
t4 w b = flatten.trans.(fmap (fmap (force.trans.mkB.(fmap mkB)))).(segment2 b b).(segment w)

-- to get the maximum performance, this is needed
diagonal = undefined
undiagonal = undefined
t5 w b = (ixMap diagonal).(t4 w b).(ixMap undiagonal)

transG :: Pull2 Grid a -> Pull2 Grid a
transG = trans

halve a = (a2 ! 0, a2 ! 1)
    where a2 = divide 2 a

zipWith :: (a -> b -> c) -> Pull d a -> Pull d b -> Pull d c
zipWith op a1 a2 =
  Pull (min (len a1) (len a2))
       (\ix -> (a1 ! ix) `op` (a2 ! ix))

class (Pushable Pull d) => SForce d where
    sforce :: (Scalar e, Scalar e2)
           => (forall d2. (SForce d2) => Pull d2 (Exp e) -> Program d2 (Push d2 (Exp e2)))
           -> Pull d (Exp e) -> Program d (Push d (Exp e2))

forOneBlock f = ForAllBlocks $ \_ -> f  --wrong implementation

instance SForce Grid where
    sforce p a | len a <= 256 = do
        return $ Push (len a) $ \wf -> do --wrong len, should be s
            forOneBlock $ do
                b <- forceP (mkB a)
                Push s f <- p b
                f wf
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

instance (Scalar t) => ToProgram (GPull (Exp t)) (GProgram a) where
  toProgram i f (Pull s ixf) = ([(nom,Pointer t)],CG.runPrg (f input))
        where nom = "input" ++ show i
              input = mkGlobal nom s
              t = typeOf_ (undefined :: t)

instance (Scalar t, ToProgram b c) => ToProgram (GPull (Exp t)) (b -> c) where
  toProgram i f ((Pull s ixf) :-> rest) = ((nom,Pointer t):ins,prg)
      where (ins,prg) = toProgram (i+1) (f input) rest
            nom = "input" ++ show i
            input = mkGlobal nom s
            t = typeOf_ (undefined :: t)

forceGP :: (Scalar e)
        => (GPull (Exp a) -> GProgram (GPush (Exp e)))
        -> GPull (Exp a) -> GProgram (GPull (Exp e))
forceGP f = (>>= forceP).f

forceG :: (Forceable a Grid e) => a Grid (Exp e) -> Program Grid (Pull Grid (Exp e))
forceG = forceP


quickPrint :: ToProgram a b => (a -> b) -> Ips a b -> IO ()
quickPrint prg input =
  putStrLn $ CUDA.genKernel "kernel" prg input

testInput :: GPull (Exp Int)
testInput = mkGlobal "apa" 256

--testPrint :: (ToProgram a b, Ips a b ~ Pull Grid (Exp Int)) => (a -> b) -> IO ()
--testPrint f = quickPrint f testInput

rh1 :: (SForce d, Scalar e, Num (Exp e)) => Pull d (Exp e) -> Program d (Push d (Exp e))
rh1 a | len a == 1 = return $ push a
rh1 a = (sforce rh1.uncurry (zipWith (+)).halve) a

trh1 :: IO ()
trh1 = quickPrint (forceGP rh1) testInput

rh2 :: (SForce d, Scalar e, Num (Exp e)) => Pull d (Exp e) -> Program d (Push d (Exp e))
rh2 a | len a == 2 = (return.push.uncurry (zipWith (+)).halve) a
rh2 a = (sforce rh2.uncurry (zipWith (+)).halve) a

trh2 :: IO ()
trh2 = quickPrint (forceGP rh2) testInput

rh3 :: (SForce d, Scalar e, Num (Exp e)) => Pull d (Exp e) -> Program d (Push d (Exp e))
rh3 a | len a == 1 = return $ push a
rh3 a = (rh3.uncurry (zipWith (+)).halve) `sforce` a

trh3 :: IO ()
trh3 = quickPrint (forceGP rh3) testInput

rh4 :: (SForce d, Scalar e, Num (Exp e)) => Pull d (Exp e) -> Program d (Push d (Exp e))
rh4 a | len a == 1 = return $ push a
rh4 a = (rh4.uncurry (zipWith (+)).halve) `sforce` a
rh4' = (rh4.uncurry (zipWith (+)).halve)

trh4 :: IO ()
trh4 = quickPrint (forceGP rh4') testInput

