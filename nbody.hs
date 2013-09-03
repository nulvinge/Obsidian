import Obsidian
import Obsidian.Dependency.Analysis
import Obsidian.Inplace
import Obsidian.Run.CUDA.Exec
import Prelude hiding (replicate,zip,abs)
import Control.Monad
import qualified Control.Monad.State as ST
import System.Random
import qualified Data.Vector.Storable as V
import qualified Data.List as L
import Graphics.Rendering.OpenGL hiding (Program)
import Graphics.UI.GLUT hiding (Program)
import Data.IORef
import Foreign.C.Types (CFloat)
import Foreign.CUDA.Driver.Graphics.OpenGL
import qualified Foreign.CUDA.Driver as CUDA
import Control.Concurrent (threadDelay)
import Data.Time.Clock


lift = ST.lift

-- http://http.developer.nvidia.com/GPUGems3/gpugems3_ch31.html

inputPos :: (SPull EFloat,SPull EFloat,SPull EFloat,SPull EFloat)
inputPos = (inputSF,inputSF,inputSF,inputSF)

inputSF :: SPull EFloat
inputSF = namedGlobal "apa" (1024*16)

eps = 1e-14

calcA :: Pos -> Pos -> Pos3 -> Program Pos3
calcA pi pj ai = do
  let bi = getPos3 pi
      bj = getPos3 pj
  r <- scalarForce $ op (-) bj bi
  dist <- scalarForce $ eps + abs r
  let invDistCube = 1 / (sqrt $ dist * dist * dist)
  s <- scalarForce $ invDistCube * getW pj
  return $ op (+) ai $ sop (*s) r

updatePos :: EFloat -> Pos3 -> (EFloat,Pos3,Pos3) -> Program (Pos3,Pos3)
updatePos t a (w,p,v) = do
  tw <- scalarForce $ t*w
  v' <- scalarForce $ op (+) (sop (tw*) a) v
  p' <- scalarForce $ op (+) p v'
  return (p',v')

getPos3 :: Pos -> Pos3
getPos3 (x,y,z,w) = (x,y,z)
getW    :: Pos -> EFloat
getW (x,y,z,w) = w
op :: (EFloat -> EFloat -> EFloat) -> Pos3 -> Pos3 -> Pos3
op o (x1,y1,z1) (x2,y2,z2) = (x1`o`x2,y1`o`y2,z1`o`z2)
sop :: (EFloat -> EFloat) -> Pos3 -> Pos3
sop f (x,y,z) = (f x, f y, f z)
abs a = add $ op (*) a a
add :: Pos3 -> EFloat
add (x,y,z) = x+y+z
zeroPos3 = (0,0,0)

type Pos = (EFloat,EFloat,EFloat,EFloat)
type Pos3 = (EFloat,EFloat,EFloat)

-- a i = G * sum $ map (\j-> m(j) * (p(j) - p(i)) / (d2(i,j) + e2) ^ (2/3))
-- d2 i j = (abs (p(j) - p(i))) ^ 2
-- e2 = e^2

nbody0 :: SPull Pos -> SPush Pos3
nbody0 arr = Push (len arr) $ \wf -> do
  forAll (n`div`256) $ \ib -> do
    ns <- names (undefined :: Pos3)
    forAll 256 $ \it -> do
      allocateScalar ns
      assignScalar ns zeroPos3
    seqFor (n`div`256) $ \jb -> do
      sh <- force $ (!jb) $ splitUp 256 arr
      forAll 256 $ \it ->
        seqFor 256 $ \jt -> do
          ai' <- calcA (arr ! (ib*256+it)) (sh ! jt) (readFrom ns)
          assignScalar ns ai'
    forAll 256 $ \it -> do
      wf (readFrom ns) (ib*256+it)
  where n=sizeConv $ len arr

nbody1 :: EFloat -> Word32 -> Word32 -> SPull (EFloat,Pos3,Pos3) -> SPush (Pos3,Pos3)
nbody1 t bs ur all =  pSplitMap bs f all
  where
    n=sizeConv $ len all
    f :: SPull (EFloat,Pos3,Pos3) -> SPush (Pos3,Pos3)
    f ball = pJoin $ do
      let barr :: SPull Pos
          barr = fmap (\(w,(x,y,z),_) -> (x,y,z,w)) ball
          arr :: SPull Pos
          arr = fmap (\(w,(x,y,z),_) -> (x,y,z,w)) all
      ais <- seqFoldA (push $ replicate bs zeroPos3) 
                      (splitUp bs arr)
                      (g barr)
      return $ pConcat $ fmap (singletonP . (uncurry $ updatePos t)) $ zip ais ball
    g :: SPull Pos -> SPull Pos3 -> SPull Pos -> SPush Pos3
    g barr ai carr = pJoin $ do
      sh <- force carr
      let sh' = splitUp ur sh
      return $ pConcatMap (singletonP . h sh') $ zip ai barr
    h :: SPull (SPull Pos) -> (Pos3,Pos) -> Program Pos3
    h sh (ai,b) = do
      seqFoldP ai sh $ \ai' cs -> do
        foldM (\ai'' i -> calcA b (cs ! fromIntegral i) ai'') ai' [0..len cs-1]

tn0 = printAnalysis (nbody0.zipp4) (inputPos :- ())
--tn1 = printAnalysis (nbody1 0.1 256 1 . zipp4) (inputPos :- ())
--tn2 = printAnalysis (nbody1 0.1 256 4 . zipp4) (inputPos :- ())

-- [(Par,Block,0),(Par,Thread,256)]
-- [(Par,Thread,4),(Seq,Thread,0)]

getPoint = getPointSphereSurf

getPointCube = do
  x <- randomRIO (-1,1 :: Float)
  y <- randomRIO (-1,1 :: Float)
  z <- randomRIO (-1,1 :: Float)
  w <- randomRIO (0.1,1 :: Float)
  return (x,y,z,w)

getPointSphereSurf = do
  (x1,x2) <- getUniCircle
  let d = x1*x1+x2*x2
      x = 2*x1*sqrt(1-d)
      y = 2*x2*sqrt(1-d)
      z = 1-2*d
  w <- randomRIO (0.1,1 :: Float)
  return (x,y,z,w)

getUniCircle = do
  x1 <- randomRIO (-1,1 :: Float)
  x2 <- randomRIO (-1,1 :: Float)
  let d = x1*x1+x2*x2
  if d >= 1
    then getUniCircle
    else return (x1,x2)


pingPongLoop :: a -> a -> (b -> CUDA ()) -> (a -> a -> CUDA b) -> CUDA ()
pingPongLoop a b display p = do
  st <- ST.get
  lift $ do
    tick <- newIORef 0
    state <- newIORef st
    dispData <- newIORef Nothing
    tt <- getCurrentTime
    time <- newIORef tt
    frameTick <- newIORef 0
    pstate <- newIORef (0,0,0)
    displayCallback $= (disp state dispData)
    idleCallback $= Just (idle tick frameTick time state dispData)
    specialCallback $= Just (specialKeyboardCallback pstate)
    mainLoop
  where
    disp state dispData = do
      d <- get dispData
      case d of
        Nothing -> return ()
        Just dd -> do
          st <- get state
          ((),st') <- ST.runStateT (display dd) st
          state $=! st'
    idle tick frameTick time state dispData = do
      t <- get tick
      st <- get state
      tick $=! (t+1)
      let (i,o) = if t `mod` 2 == 0 then (a,b) else (b,a)
      (dispD,st') <- ST.runStateT (p i o) st
      state $=! st'
      dispData $=! (Just dispD)
      if t `mod` 1 /= 0
        then return ()
        else do
          tt <- get time
          tt' <- getCurrentTime
          time $= tt'
          ft <- get frameTick
          frameTick $= (t+1)
          CUDA.sync
          let size = 32*1024
              frames = (t+1-ft)
              time = diffUTCTime tt' tt
              flop = (fromIntegral $ (size*size*20 + size*10) * frames) / 1e9
          putStrLn $ "FPS: " ++ show (fromIntegral frames / time)
                  ++ "\tframes:" ++ show frames
                  ++ "\ttime:"   ++ show time
                  ++ "\tGFLOP:"   ++ show flop
                  ++ "\tGFLOPs:"  ++ show (flop / time)
          postRedisplay Nothing

runVector = do 
  (progname, _) <- getArgsAndInitialize
  initialDisplayMode $= [DoubleBuffered]
  createWindow "Hello World"
  let size = 16*1024
  withCUDA True $ do
    let inputV :: SPull EFloat3
        inputV = namedGlobal "apa" $ fromIntegral size
        inputP :: SPull EFloat4
        inputP = namedGlobal "apa" $ fromIntegral size
        wrap :: SPull EFloat4 -> SPull EFloat3 -> SPush (EFloat4,EFloat3)
        wrap p v = let (x,y,z,w) = unzipp4 $ fmap fromVector p
                       a = nbody1 0.000000001 256 4 $ zipp3 (w,zipp3 (x,y,z),fmap fromVector v)
                   in imap (\ix ((x',y',z'),v') -> (toVector (x',y',z',1.0), toVector v')) a
    kern <- capture wrap (inputP :- inputV :- ())
    {-
        wrap :: SPush (EFloat2)
        wrap     = let (x,y,z,w) = unzipp4 $ replicate (16*1024) (0,0,0,0)
                       a = nbody1 0.000000001 256 1 $ zipp3 (w,zipp3 (x,y,z),replicate (len x) (0,0,0))
                   in imap (\ix ((x,y,z),(vx,vy,vz)) -> toVector (x,y)) a
    kern <- capture wrap (())
    -}
    points <- lift $ mapM (const getPoint) [0..size-1]
    let p1 = L.concat $ map (\(x,y,z,w) -> [x,y,z,w]) $ points
        p2 = fmap (*0) p1
        v = L.concat $ L.replicate size [0,0,0]

    useGLVectors (map V.fromList [p1,p2]) $ \[p1,p2] -> do
      useVectors [v,v] $ \[v1,v2] -> do
        pingPongLoop (p1,v1) (p2,v2) (display) $ \((p1,_),v1) ((p2,pd),v2) -> do
          withMappedResources [p1,p2] $ \[p1,p2] -> do
            () <== (fixOutputs (kern <^> p1 <^^^> v1) (p2,v2))
            sync

            -- px <- peekCUDAVector x2
            -- py <- peekCUDAVector y2
            -- pz <- peekCUDAVector z2
            -- ri <- peekCUDAVector x1
            -- lift $ putStrLn $ show $ foldr1 max $ L.zipWith (-) px ri
            -- return $ zip3 px py pz
            return $ (pd,size)
  where
    display (pd,size) = lift $ do
      clear [ColorBuffer,DepthBuffer]
      -- renderPrimitive Points $ mapM_ (\(x,y,z)-> vertex $ Vertex3 (cFloat x) (cFloat y) (cFloat z)) $ dispD
      drawBufferObject pd size Points 4
      swapBuffers

    fixOutputs :: KernelT (SPush (Exp a, Exp b)) -> (CUDAVector a,CUDAVector Float) -> KernelT () 
    fixOutputs (KernelT f t bb s i o) (a,b) = KernelT f t bb s i (o ++ [CUDA.VArg (cvPtr a),CUDA.VArg (cvPtr b)])

runNormal = do 
  (progname, _) <- getArgsAndInitialize
  createWindow "Hello World"
  withCUDA True $ do
    let input = namedGlobal "apa" (16*1024)
    kern <- capture (\w x y z vx vy vz -> nbody1 0.000000001 256 1 $ zipp3 (w,zipp3 (x,y,z),zipp3 (vx,vy,vz)))
                    (input :- input :- input :- input :- input :- input :- input :- ())
    points <- lift $ mapM (const getPoint) [0..len input-1]
    let (x,y,z,w) = L.unzip4 $ points
        x0 = map (*0) x

    useVectors [w,x,y,z,x0,x0,x0,x0,x0,x0,x0,x0,x0] $ \[w,x1,y1,z1,x2,y2,z2,vx1,vy1,vz1,vx2,vy2,vz2] -> do
      pingPongLoop (x1,y1,z1,vx1,vy1,vz1) (x2,y2,z2,vx2,vy2,vz2) display $ \(x1,y1,z1,vx1,vy1,vz1) (x2,y2,z2,vx2,vy2,vz2) -> do
        ((x2,y2,z2),(vx2,vy2,vz2)) <== kern <> w <> x1 <> y1 <> z1 <> vx1 <> vy1 <> vz1
        sync

        px <- peekCUDAVector x2
        py <- peekCUDAVector y2
        pz <- peekCUDAVector z2
        --ri <- peekCUDAVector x1
        --lift $ putStrLn $ show $ foldr1 max $ L.zipWith (-) px ri
        --lift $ putStrLn $ show $ L.take 10 $ (zip3 px py pz)
        return $ zip3 px py pz
  where
    display dispD = lift $ do
      clear [ColorBuffer,DepthBuffer]
      renderPrimitive Points $ mapM_ (\(x,y,z)-> vertex $ Vertex3 (cFloat x) (cFloat y) (cFloat z)) $ dispD
      swapBuffers

runInterop = do 
  (progname, _) <- getArgsAndInitialize
  createWindow "Hello World"
  withCUDA True $ do
    let input = namedGlobal "apa" (32*1024)
    kern <- capture (\w x y z vx vy vz -> nbody1 0.000000001 256 1 $ zipp3 (w,zipp3 (x,y,z),zipp3 (vx,vy,vz)))
                    (input :- input :- input :- input :- input :- input :- input :- ())
    restructureKern <- captureWithStrategy [(Par,Block,32),(Par,Thread,512),(Seq,Thread,0)] rest3
                    (input :- input :- input :- ())
    points <- lift $ mapM (const getPoint) [0..len input-1]
    let (x,y,z,w) = L.unzip4 $ points
        x0 = map (const 0) x
        d = L.replicate (4*length points) (0 :: Float)

    useVectors [w,x,y,z,x0,x0,x0,x0,x0,x0,x0,x0,x0] $ \[w,x1,y1,z1,x2,y2,z2,vx1,vy1,vz1,vx2,vy2,vz2] -> do
      useGLVectors [V.fromList d] $ \[d] -> do
        pingPongLoop (x1,y1,z1,vx1,vy1,vz1) (x2,y2,z2,vx2,vy2,vz2) (display restructureKern) $ \(x1,y1,z1,vx1,vy1,vz1) (x2,y2,z2,vx2,vy2,vz2) -> do
          ((x2,y2,z2),(vx2,vy2,vz2)) <== kern <> w <> x1 <> y1 <> z1 <> vx1 <> vy1 <> vz1
          return $ (d,length points,x2,y2,z2)
  where
    display restructureKern (d,size,x2,y2,z2) = do
      withMappedResources [fst d] $ \[d] -> do
        d <== restructureKern <> x2 <> y2 <> z2
      lift $ clear [ColorBuffer,DepthBuffer]
      lift $ drawBufferObject (snd d) size Points 4
      lift $ swapBuffers
    rest3 :: SPull EFloat -> SPull EFloat -> SPull EFloat -> SPush EFloat
    rest3 x y z = pSplitMap 8 (pConcatMap rf3) $ zipp3 (x,y,z)
    rf3 (x,y,z) = 
      Push 4 $ \wf -> do
        wf x 0
        wf y 1
        wf z 2
        wf 1 3

main = runInterop

--Threads per Block: 32
--Blocks: 128


cFloat :: Float -> CFloat
cFloat = fromRational . toRational 

pp a = do
  ri <- peekCUDAVector a
  lift $ putStrLn $ show $ head ri

data ProgramState = ProgramState
  { axes :: (String,String,String)
  , camerarotation :: (Float,Float,Float)
  }

specialKeyboardCallback state KeyUp _ = do
  (x,y,z) <- readIORef state
  state `writeIORef` (x+3,y,z)
specialKeyboardCallback state KeyDown _ = do
  (x,y,z) <- readIORef state
  state `writeIORef` (x-3,y,z)
specialKeyboardCallback state KeyRight _ = do
  (x,y,z) <- readIORef state
  state `writeIORef` (x,y+3,z)
specialKeyboardCallback state KeyLeft _ = do
  (x,y,z) <- readIORef state
  state `writeIORef` (x,y-3,z)
specialKeyboardCallback _ _ _ = return ()

