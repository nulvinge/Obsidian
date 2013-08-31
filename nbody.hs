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
  v' <- scalarForce $ op (+) (sop ((t*w)*) a) v
  let p' = op (+) p v'
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

seqFoldAII :: (MemoryOps a)
           => EWord32
           -> SPush a
           -> (EWord32 -> SPull a -> SPush a)
           -> Program (SPull a)
seqFoldAII n a f = do
  t <- forceInplace a
  seqFor n $ \i -> do
    let t' = f i (pullInplace t)
    t'' <- force t'
    inplaceForce t $ push t''
  return $ pullInplace t

seqFoldA :: (ASize l, MemoryOps a)
         => SPush a
         -> Pull l b
         -> (SPull a -> b -> SPush a)
         -> Program (SPull a)
seqFoldA a arr f = seqFoldAII (sizeConv $ len arr) a
                              (\i a -> f a (arr!i))

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


pingPongLoop :: a -> a -> (a -> a -> CUDA [(Float,Float,Float)]) -> CUDA ()
pingPongLoop a b p = do
  st <- ST.get
  lift $ do
    tick <- newIORef 0
    state <- newIORef st
    dispData <- newIORef []
    (progname, _) <- getArgsAndInitialize
    createWindow "Hello World"
    displayCallback $= (display dispData)
    idleCallback $= Just (idle tick state dispData)
    mainLoop
  where
    idle tick state dispData = do
      t <- get tick
      st <- get state
      tick $=! (t+1)
      (dispD,st') <- if t `mod` 2 == 0
        then
          ST.runStateT (p a b) st
        else
          ST.runStateT (p b a) st
      state $=! st'
      dispData $=! dispD
      if t `mod` 8 == 0
        then postRedisplay Nothing
        else return ()
    display dispData = do
      dispD <- get dispData
      clear [ColorBuffer]
      renderPrimitive Points $ mapM_ (\(x,y,z)-> vertex $ Vertex3 (cFloat x) (cFloat y) (cFloat z)) $ dispD
      flush

useVectors :: V.Storable a => [[a]] -> ([CUDAVector a] -> CUDA b) -> CUDA b
useVectors l p = useVectors' [] l p
useVectors' vl [] p = p $ L.reverse vl
useVectors' vl (v:l) p = useVector (V.fromList v) $ \vv -> useVectors' (vv:vl) l p

performSmall = withCUDA $ do
  let input = namedGlobal "apa" (16*1024)
  --kern <- capture (\x y z w -> push $ fmap getPos3 $ zipp4 (x,y,z,w))
  kern <- capture (\w x y z vx vy vz -> nbody1 0.000000001 256 1 $ zipp3 (w,zipp3 (x,y,z),zipp3 (vx,vy,vz)))
                  (input :- input :- input :- input :- input :- input :- input :- ())
  points <- lift $ mapM (const getPoint) [0..len input-1]
  let (x,y,z,w) = L.unzip4 $ points
      x0 = map (*0) x

  useVectors [w,x,y,z,x0,x0,x0,x0,x0,x0,x0,x0,x0] $ \[w,x1,y1,z1,x2,y2,z2,vx1,vy1,vz1,vx2,vy2,vz2] -> do
    pingPongLoop (x1,y1,z1,vx1,vy1,vz1) (x2,y2,z2,vx2,vy2,vz2) $ \(x1,y1,z1,vx1,vy1,vz1) (x2,y2,z2,vx2,vy2,vz2) -> do
      ((x2,y2,z2),(vx2,vy2,vz2)) <== kern <> w <> x1 <> y1 <> z1 <> vx1 <> vy1 <> vz1


      px <- peekCUDAVector x2
      py <- peekCUDAVector y2
      pz <- peekCUDAVector z2
      ri <- peekCUDAVector x1
      lift $ putStrLn $ show $ foldr1 max $ L.zipWith (-) px ri
      return $ zip3 px py pz

cFloat :: Float -> CFloat
cFloat = fromRational . toRational 

pp a = do
  ri <- peekCUDAVector a
  lift $ putStrLn $ show $ head ri

