{-# LANGUAGE TypeOperators,
             ScopedTypeVariables,
             TypeFamilies,
             TypeSynonymInstances,
             FlexibleInstances #-} 

module Obsidian.Run.CUDA.Exec where

---------------------------------------------------------------------------
--
-- Low level interface to CUDA functionality from Obsidian
--
---------------------------------------------------------------------------


import qualified Foreign.CUDA.Driver as CUDA
import qualified Foreign.CUDA.Driver.Device as CUDA
import qualified Foreign.CUDA.Analysis.Device as CUDA
import qualified Foreign.CUDA.Driver.Stream as CUDAStream
import qualified Foreign.CUDA.Driver.Graphics as CUGL
import qualified Foreign.CUDA.Driver.Graphics.OpenGL as CUGL
import qualified Graphics.Rendering.OpenGL as GL

import Obsidian.CodeGen.Program
import Obsidian.CodeGen.InOut
import qualified Obsidian.CodeGen.CUDA as CG

import Obsidian.Types -- experimental
import Obsidian.Exp
import Obsidian.Globs
import Obsidian.Array
import Obsidian.Program (Program)
-- import Obsidian.Mutable

import Foreign.Marshal.Array
import Foreign.ForeignPtr.Unsafe -- (req GHC 7.6 ?)
import Foreign.ForeignPtr hiding (unsafeForeignPtrToPtr)
import Foreign.Ptr (nullPtr)

import qualified Data.Vector.Storable as V 
import qualified Foreign.Storable as V 

import Data.Word
import Data.Int
import Data.Supply
import Data.List
import qualified Data.Map as M
import Data.Maybe

import System.IO.Unsafe
import System.Process 

import Control.Monad.State



debug = True


---------------------------------------------------------------------------
-- An array located in GPU memory
---------------------------------------------------------------------------
data CUDAVector a = CUDAVector {cvPtr :: CUDA.DevicePtr a,
                                cvLen :: Word32} 

---------------------------------------------------------------------------
-- Get a list of devices from the CUDA driver
---------------------------------------------------------------------------
getDevices :: IO [(CUDA.Device,CUDA.DeviceProperties)]
getDevices = do
  num <- CUDA.count 
  devs <- mapM CUDA.device [0..num-1]
  props <- mapM CUDA.props devs
  return $ zip devs props

---------------------------------------------------------------------------
-- Print a Summary of a device's properties. 
---------------------------------------------------------------------------
propsSummary :: CUDA.DeviceProperties -> String
propsSummary props = unlines
  ["Device Name: " ++ CUDA.deviceName props,
   "Compute Cap: " ++ show (CUDA.computeCapability props),
   "Global Mem:  " ++ show (CUDA.totalGlobalMem props),
   "Shared Mem/Block: " ++ show (CUDA.sharedMemPerBlock props),
   "Registers/Block: "  ++ show (CUDA.regsPerBlock props),
   "Warp Size: " ++ show (CUDA.warpSize props),
   "Max threads/Block: " ++ show (CUDA.maxThreadsPerBlock props),
   "Max threads/MP: " ++ show (CUDA.maxThreadsPerMultiProcessor props),
   "Clock rate: " ++ show (CUDA.clockRate props),
   "Num MP: " ++ show (CUDA.multiProcessorCount props),
   "Mem bus width: " ++ show (CUDA.memBusWidth props)] 

--------------------------------------------------------------------------
-- Environment to run CUDA computations in.
--  # Needs to keep track of generated and loaded functions etc. 
---------------------------------------------------------------------------

data CUDAState = CUDAState { csIdent :: Int,
                             csCtx   :: CUDA.Context,
                             csProps :: CUDA.DeviceProperties}

type CUDA a =  StateT CUDAState IO a

data Kernel = Kernel {kFun :: CUDA.Fun,
                      kThreadsPerBlock :: Word32,
                      kSharedBytes :: Word32}

-- Change so that the type parameter to KernelT
-- represents the "captured" type, with CUDAVectors instead of Pull, Push vectors. 
data KernelT a = KernelT {ktFun :: CUDA.Fun,
                          ktThreadsPerBlock :: Word32,
                          ktBlocks :: Word32,
                          ktSharedBytes :: Word32,
                          ktInputs :: [CUDA.FunParam],
                          ktOutput :: [CUDA.FunParam] }

---------------------------------------------------------------------------
-- Kernel Input and Output classes
---------------------------------------------------------------------------
class KernelI a where
  type KInput a 
  addInParam :: KernelT (KInput a -> b) -> a -> KernelT b

class KernelM a where
  type KMutable a
  addMutable :: KernelT (KMutable a -> b) -> a -> KernelT b 
  
class KernelO a where
  type KOutput a 
  addOutParam :: KernelT (KOutput a) -> a -> KernelT () 

{-
instance Scalar a => KernelI (CUDAVector a) where
  type KInput (CUDAVector a) = DPull (Exp a) 
  addInParam (KernelT f t s i o) b =
    KernelT f t s (i ++ [CUDA.VArg (cvPtr b),
                         CUDA.VArg (cvLen b)]) o
-}

instance Scalar a => KernelI (CUDAVector a) where
  type KInput (CUDAVector a) = SPull (Exp a) 
  addInParam (KernelT f t bb s i o) b =
    KernelT f t bb s (CUDA.VArg (cvPtr b) : i) o

{-
instance Scalar a => KernelM (CUDAVector a) where
  type KMutable (CUDAVector a) = Mutable Global (Exp a) 
  addMutable (KernelT f t s i o) b =
    KernelT f t s (i ++ [CUDA.VArg (cvPtr b),
                         CUDA.VArg (cvLen b)]) o
-}

instance KernelO () where
  type KOutput () = ()
  addOutParam k () = k

instance Scalar a => KernelO (CUDAVector a) where
  type KOutput (CUDAVector a) = SPush (Exp a) 
  addOutParam (KernelT f t bb s i o) b =
    KernelT f t bb s i (o ++ [CUDA.VArg (cvPtr b)])

instance (Scalar a, Scalar b) => KernelO (CUDAVector a, CUDAVector b) where
  type KOutput (CUDAVector a,CUDAVector b) = SPush (Exp a, Exp b)
  addOutParam (KernelT f t bb s i o) (a,b) =
    KernelT f t bb s i (o ++ [CUDA.VArg (cvPtr a),CUDA.VArg (cvPtr b)])

instance (Scalar a, Scalar b, Scalar c)
    => KernelO (CUDAVector a, CUDAVector b, CUDAVector c) where
  type KOutput (CUDAVector a, CUDAVector b, CUDAVector c) = SPush (Exp a, Exp b, Exp c)
  addOutParam (KernelT f t bb s i o) (a,b,c) =
    KernelT f t bb s i (o ++ [CUDA.VArg (cvPtr a),CUDA.VArg (cvPtr b),CUDA.VArg (cvPtr c)])

instance (Scalar a, Scalar b, Scalar c, Scalar d, Scalar e, Scalar f)
    => KernelO ((CUDAVector a, CUDAVector b, CUDAVector c), (CUDAVector d, CUDAVector e, CUDAVector f)) where
  type KOutput ((CUDAVector a, CUDAVector b, CUDAVector c), (CUDAVector d, CUDAVector e, CUDAVector f))
          = SPush ((Exp a, Exp b, Exp c),(Exp d, Exp e, Exp f))
  addOutParam (KernelT ff t bb s i o) ((a,b,c),(d,e,f)) =
    KernelT ff t bb s i (o ++ [CUDA.VArg (cvPtr a),CUDA.VArg (cvPtr b),CUDA.VArg (cvPtr c),CUDA.VArg (cvPtr d),CUDA.VArg (cvPtr e),CUDA.VArg (cvPtr f)])

---------------------------------------------------------------------------
-- (<>) apply a kernel to an input
---------------------------------------------------------------------------
(<>) :: KernelI a => KernelT (KInput a -> b) -> a -> KernelT b
(<>) kern a = addInParam kern a

(<^>) :: KernelT (SPull (Exp a) -> b) -> CUDAVector a -> KernelT b
(<^>) (KernelT f t bb s i o) b = KernelT f t bb s (CUDA.VArg (cvPtr b) : i) o

(<^^>) :: KernelT (SPull (Exp (a,a)) -> b) -> CUDAVector a -> KernelT b
(<^^>) (KernelT f t bb s i o) b = KernelT f t bb s (CUDA.VArg (cvPtr b) : i) o

(<^^^>) :: KernelT (SPull (Exp (a,a,a)) -> b) -> CUDAVector a -> KernelT b
(<^^^>) (KernelT f t bb s i o) b = KernelT f t bb s (CUDA.VArg (cvPtr b) : i) o

---------------------------------------------------------------------------
-- Assign a mutable input/output to a kernel
--------------------------------------------------------------------------- 
(<:>) :: KernelM a
         => KernelT (KMutable a -> b) -> a -> KernelT b
(<:>) kern a = addMutable kern a


---------------------------------------------------------------------------
-- Execute a kernel and store output to an array
---------------------------------------------------------------------------
(<==) :: KernelO b => b -> KernelT (KOutput b) -> CUDA ()
(<==) o kern =
  do
    let k = addOutParam kern o
    when (False && debug) $ do
      lift $ putStrLn $ "B: " ++ show (fromIntegral (ktBlocks k),1,1)
                     ++ " T: " ++ show (fromIntegral (ktThreadsPerBlock k), 1, 1)
    lift $ CUDA.launchKernel
      (ktFun k)
      (fromIntegral (ktBlocks k),1,1)
      (fromIntegral (ktThreadsPerBlock k), 1, 1)
      (fromIntegral (ktSharedBytes k))
      Nothing -- stream
      (ktInputs k ++ ktOutput k) -- params    

sync :: CUDA ()
sync = lift $ CUDA.sync

-- Tweak these 
infixl 4 <>
infixl 4 <^>
infixl 4 <^^>
infixl 4 <^^^>
infixl 3 <==

---------------------------------------------------------------------------
-- Execute a kernel that has no Output ( a -> GProgram ()) KernelT (GProgram ()) 
---------------------------------------------------------------------------
exec :: (Word32, KernelT (Program ())) -> CUDA ()
exec (nb, k) = 
  lift $ CUDA.launchKernel
      (ktFun k)
      (fromIntegral nb,1,1)
      (fromIntegral (ktThreadsPerBlock k), 1, 1)
      (fromIntegral (ktSharedBytes k))
      Nothing -- stream
      (ktInputs k)
---------------------------------------------------------------------------
-- Get a fresh identifier
---------------------------------------------------------------------------
newIdent :: CUDA Int
newIdent =
  do
    i <- gets csIdent
    modify (\s -> s {csIdent = i+1 }) 
    return i


---------------------------------------------------------------------------
-- Run a CUDA computation
---------------------------------------------------------------------------
--if useGL == True:
--remember to initialize GLUT and create a rendering context (create a window)

withCUDA useGL p =
  do
    CUDA.initialise []
    devs <- getDevices
    case devs of
      [] -> error "No CUDA device found!" 
      (x:xs) ->
        do 
          ctx <- (if useGL then CUGL.createGLContext else CUDA.create) (fst x) [CUDA.SchedAuto]
          runStateT p (CUDAState 0 ctx (snd x)) 
          CUDA.destroy ctx

---------------------------------------------------------------------------
-- Capture without an inputlist! 
---------------------------------------------------------------------------    

capture :: ToProgram prg => prg -> InputList prg -> CUDA (KernelT prg) 
capture = captureWithStrategy defaultStrategy

captureWithStrategy :: ToProgram prg => Strategy -> prg -> InputList prg -> CUDA (KernelT prg) 
captureWithStrategy strat f a =
  do
    i <- newIdent

    props <- return . csProps =<< get
    
    let kn     = "gen" ++ show i
        fn     = kn ++ ".cu"
        cub    = fn ++ ".cubin"

        (prgstr,bytesShared,blocks,threadsPerBlock) = CG.genKernelM kn strat f a
        header = "#include <stdint.h>\n" -- more includes ? 

    when debug $ 
      do 
        lift $ putStrLn $ prgstr
        lift $ putStrLn $ "Bytes shared mem: " ++ show bytesShared
        lift $ putStrLn $ "Threads per Block: " ++ show threadsPerBlock
        lift $ putStrLn $ "Blocks: " ++ show blocks

    let arch = archStr props
        
    lift $ storeAndCompile arch (fn) (header ++ prgstr)
    
    mod <- liftIO $ CUDA.loadFile cub
    fun <- liftIO $ CUDA.getFun mod kn 

    {- After loading the binary into the running process
       can I delete the .cu and the .cu.cubin ? -} 
           
    return $ KernelT fun threadsPerBlock blocks bytesShared [] []



---------------------------------------------------------------------------
-- useVector: Copies a Data.Vector from "Haskell" onto the GPU Global mem 
--------------------------------------------------------------------------- 
useVector :: V.Storable a =>
             V.Vector a -> (CUDAVector a -> CUDA b) -> CUDA b
useVector v f =
  do
    let (hfptr,n) = V.unsafeToForeignPtr0 v
    
    dptr <- lift $ CUDA.mallocArray n
    let hptr = unsafeForeignPtrToPtr hfptr
    lift $ CUDA.pokeArray n hptr dptr
    let cvector = CUDAVector dptr (fromIntegral (V.length v))
    b <- f cvector -- dptr     
    lift $ CUDA.free dptr
    return b

useVectors :: V.Storable a => [[a]] -> ([CUDAVector a] -> CUDA b) -> CUDA b
useVectors l p = useVectors' [] l p
  where
    useVectors' vl [] p = p $ reverse vl
    useVectors' vl (v:l) p = useVector (V.fromList v) $ \vv -> useVectors' (vv:vl) l p

useGLVectors :: V.Storable a =>
                [V.Vector a] -> ([(CUGL.Resource, GL.BufferObject)] -> CUDA b) -> CUDA b
useGLVectors vs f =
  do
    buffs <- lift $ GL.genObjectNames $ length vs
    ress <- mapM makeResource $ zip vs buffs
    withMappedResources ress $ \devs -> do
      mapM writeArrays $ zip vs devs

    b <- f $ zip ress buffs

    lift $ mapM CUGL.unregisterResource ress
    lift $ GL.deleteObjectNames buffs
    
    return b

  where makeResource (v,buff) = do
          lift $ GL.bindBuffer GL.ArrayBuffer GL.$= (Just buff)
          let size = fromIntegral $ V.sizeOf (V.head v) * 4*V.length v
          lift $ GL.bufferData GL.ArrayBuffer GL.$= (size, nullPtr, GL.DynamicDraw)
          lift $ GL.bindBuffer GL.ArrayBuffer GL.$= Nothing
          lift $ CUGL.registerBuffer buff CUGL.RegisterNone
        writeArrays (v,CUDAVector dev n) = do
          let (hfptr,n) = V.unsafeToForeignPtr0 v
          let hptr = unsafeForeignPtrToPtr hfptr
          lift $ CUDA.pokeArray n hptr dev

withMappedResources :: [CUGL.Resource] -> ([CUDAVector a] -> CUDA b) -> CUDA b
withMappedResources ress f = do
  lift $ CUGL.mapResources ress Nothing
  ps <- lift $ mapM CUGL.getMappedPointer ress
  let elemsize = 4*4
  let cvectors = map (\(devptr,n) -> CUDAVector devptr (fromIntegral n `div` elemsize)) ps
  b <- f cvectors
  lift $ CUGL.unmapResources ress Nothing
  return b

drawBufferObject bo size tt coords = do
  GL.bindBuffer GL.ArrayBuffer GL.$= Just bo
  GL.arrayPointer GL.VertexArray GL.$= (GL.VertexArrayDescriptor coords GL.Float 0 nullPtr)
  GL.clientState GL.VertexArray GL.$= GL.Enabled
  GL.drawArrays tt 0 (fromIntegral size)
  GL.clientState GL.VertexArray GL.$= GL.Disabled
  GL.bindBuffer GL.ArrayBuffer GL.$= Nothing

---------------------------------------------------------------------------
-- allocaVector: allocates room for a vector in the GPU Global mem
---------------------------------------------------------------------------
allocaVector :: V.Storable a => 
                Int -> (CUDAVector a -> CUDA b) -> CUDA b                
allocaVector n f =
  do
    dptr <- lift $ CUDA.mallocArray n
    let cvector = CUDAVector dptr (fromIntegral n)
    b <- f cvector -- dptr
    lift $ CUDA.free dptr
    return b 

---------------------------------------------------------------------------
-- Allocate and fill with default value
---------------------------------------------------------------------------
allocaFillVector :: V.Storable a => 
                Int -> a -> (CUDAVector a -> CUDA b) -> CUDA b                
allocaFillVector n a f =
  do
    dptr <- lift $ CUDA.mallocArray n
    lift $ CUDA.memset dptr n a 
    let cvector = CUDAVector dptr (fromIntegral n)
    b <- f cvector -- dptr
    lift $ CUDA.free dptr
    return b 

---------------------------------------------------------------------------
-- Fill a Vector
---------------------------------------------------------------------------
fill :: V.Storable a =>
        CUDAVector a -> 
        a -> CUDA ()
fill (CUDAVector dptr n) a =
  lift $ CUDA.memset dptr (fromIntegral n) a 

---------------------------------------------------------------------------
-- Peek in a CUDAVector (Simple "copy back")
---------------------------------------------------------------------------
peekCUDAVector :: V.Storable a => CUDAVector a -> CUDA [a]
peekCUDAVector (CUDAVector dptr n) = 
    lift $ CUDA.peekListArray (fromIntegral n) dptr

copyOut :: V.Storable a => CUDAVector a -> CUDA (V.Vector a)
copyOut (CUDAVector dptr n) =
  do
    (fptr :: ForeignPtr a) <- lift $ mallocForeignPtrArray (fromIntegral n)
    let ptr = unsafeForeignPtrToPtr fptr
    lift $ CUDA.peekArray (fromIntegral n) dptr ptr
    return $ V.unsafeFromForeignPtr fptr 0 (fromIntegral n)

---------------------------------------------------------------------------
-- Get the "architecture" of the present CUDA device
---------------------------------------------------------------------------
  
archStr :: CUDA.DeviceProperties -> String
archStr props = "-arch=sm_" ++ archStr' (CUDA.computeCapability props)
  where
    -- Updated for Cuda bindings version 0.5.0.0
    archStr' (CUDA.Compute h l) = show h ++ show l
    --archStr' (CUDA.Compute 1 0) = "10"
    --archStr' (CUDA.Compute 1 2) = "12"
    --archStr' (CUDA.Compute 2 0) = "20" 
    --archStr' (CUDA.Compute 3 0) = "30"
    --archStr' x = error $ "Unknown architecture: " ++ show x 
    
---------------------------------------------------------------------------
-- Compile to Cubin (interface with nvcc)
---------------------------------------------------------------------------
storeAndCompile :: String -> FilePath -> String -> IO FilePath
storeAndCompile arch fp code =
  do
    writeFile fp code
    
    let nfp = fp ++  ".cubin"

    (_,_,_,pid) <-
      createProcess (shell ("nvcc " ++ arch ++ " -cubin -o " ++ nfp ++ " " ++ fp))
    exitCode <- waitForProcess pid
    return nfp

