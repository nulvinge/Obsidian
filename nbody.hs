import Obsidian
import Obsidian.Dependency.Analysis
import Obsidian.Inplace
import Obsidian.Run.CUDA.Exec
import Prelude hiding (replicate,zip,abs)
import Control.Monad
import Control.Monad.State
import System.Random
import qualified Data.Vector.Storable as V
import qualified Data.List as L
import Graphics.Rendering.OpenGL hiding (Program)
import Graphics.UI.GLUT hiding (Program)

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
  r <- scalarForce $ op (-) bi bj
  dist <- scalarForce $ eps + abs r
  let invDistCube = 1 / (sqrt $ dist * dist * dist)
  s <- scalarForce $ invDistCube * getW pj
  return $ op (+) ai $ sop (*s) r

updatePos :: EFloat -> Pos3 -> Pos -> Pos3
updatePos t a p = op (+) (sop ((t*getW p)*) a) $ getPos3 p

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

nbody1 :: EFloat -> Word32 -> Word32 -> SPull Pos -> SPush Pos3
nbody1 t bs ur arr = pSplitMap bs (pJoin . fmap push . f) arr
  where
    n=sizeConv $ len arr
    f :: SPull Pos -> Program (SPull Pos3)
    f barr = do
      ais <- seqFoldA (push $ replicate bs zeroPos3) 
                      (splitUp bs arr) (g barr)
      return $ fmap (uncurry $ updatePos t) $ zip ais barr
      --return ais
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
tn1 = printAnalysis (nbody1 0.1 256 1 . zipp4) (inputPos :- ())
tn2 = printAnalysis (nbody1 0.1 256 4 . zipp4) (inputPos :- ())

-- [(Par,Block,0),(Par,Thread,256)]
-- [(Par,Thread,4),(Seq,Thread,0)]


getPoint = do
  x <- randomRIO (0,1)
  y <- randomRIO (0,1)
  z <- randomRIO (0,1)
  w <- randomRIO (0.1,1)
  return (x,y,z,w)

pingPongLoop a b p = do
  p a b
  pingPongLoop b a p

useVectors :: V.Storable a => [[a]] -> ([CUDAVector a] -> CUDA b) -> CUDA b
useVectors l p = useVectors' [] l p
useVectors' vl [] p = p $ L.reverse vl
useVectors' vl (v:l) p = useVector (V.fromList v) $ \vv -> useVectors' (vv:vl) l p

performSmall = withCUDA $ do
  let input = namedGlobal "apa" (16*1024)
  --kern <- capture (\x y z w -> push $ fmap getPos3 $ zipp4 (x,y,z,w))
  kern <- capture (\x y z w -> nbody1 0.00000001 256 1 $ zipp4 (x,y,z,w))
                  (input :- input :- input :- input :- ())
  points <- lift $ mapM (const getPoint) [0..len input-1]
  let (x,y,z,w) = L.unzip4 $ points
      x0 = map (*0) x

  useVectors [x,y,z,x0,x0,x0,w] $ \[x1,y1,z1,x2,y2,z2,w] -> do
    pingPongLoop (x1,y1,z1) (x2,y2,z2) $ \(x1,y1,z1) (x2,y2,z2) -> do
      sync
      lift $ putStrLn "test1"
      pp x2
      pp y2
      pp z2
      (x2,y2,z2) <== kern <> x1 <> y1 <> z1 <> w
      sync
      lift $ putStrLn "test2"
      pp x1
      pp y1
      pp z1
      pp w
      pp x2
      pp y2
      pp z2
      lift $ putStrLn "test2"
      ri <- peekCUDAVector x1
      ro <- peekCUDAVector x2
      sync
      lift $ putStrLn "test3"
      lift $ putStrLn $ show $ foldr1 max $ L.zipWith (-) ro ri
      --lift $ putStrLn $ show $ L.zip ro ri
      --lift $ putStrLn $ show $ ro
      --lift $ putStrLn $ show $ ro

pp a = do
  ri <- peekCUDAVector a
  lift $ putStrLn $ show $ head ri
  
myPoints :: [(GLfloat,GLfloat,GLfloat)]
myPoints = map (\k -> (sin(2*pi*k/12),cos(2*pi*k/12),0.0)) [1..12]
main = do 
  (progname, _) <- getArgsAndInitialize
  createWindow "Hello World"
  displayCallback $= display
  mainLoop
display = do 
  clear [ColorBuffer]
  renderPrimitive Points $ mapM_ (\(x, y, z)->vertex$Vertex3 x y z) myPoints
  flush


















