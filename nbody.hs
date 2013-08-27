import Obsidian
import Obsidian.Dependency.Analysis
import Obsidian.Inplace
import Prelude hiding (replicate,zip)

-- http://http.developer.nvidia.com/GPUGems3/gpugems3_ch31.html

inputPos :: (SPull EFloat,SPull EFloat,SPull EFloat,SPull EFloat)
inputPos = (inputSF,inputSF,inputSF,inputSF)

inputSF :: SPull EFloat
inputSF = namedGlobal "apa" (1024*16)

calcA :: Pos -> Pos -> Pos3 -> Program Pos3
calcA pi pj ai = do
  let bi = getPos3 pi
      bj = getPos3 pj
  r <- forceScalar "r" $ op (-) bi bj
  dist <- forceScalar "dist" $ add $ op (*) r r
  let invDistCube = 1 / (sqrt $ dist * dist * dist)
  s <- forceScalar "s" $ invDistCube * getW pj
  return $ op (+) ai $ sop (*s) r

getPos3 :: Pos -> Pos3
getPos3 (x,y,z,w) = (x,y,z)
getW    :: Pos -> EFloat
getW (x,y,z,w) = w
op :: (EFloat -> EFloat -> EFloat) -> Pos3 -> Pos3 -> Pos3
op o (x1,y1,z1) (x2,y2,z2) = (x1`o`x2,y1`o`y2,z1`o`z2)
sop :: (EFloat -> EFloat) -> Pos3 -> Pos3
sop f (x,y,z) = (f x, f y, f z)
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


nbody1 :: SPull Pos -> SPush Pos3
nbody1 arr = pSplitMap (256 :: Word32) (pJoin . fmap push . f) arr
  where
    n=sizeConv $ len arr
    f :: SPull Pos -> Program (SPull Pos3)
    f barr = do
      seqFoldA (push $ replicate 256 zeroPos3) 
               (splitUp 256 arr) (g barr)
    g :: SPull Pos -> SPull Pos3 -> SPull Pos -> SPush Pos3
    g barr ai carr = pJoin $ do
      sh <- force carr
      return $ pConcatMap (singletonP . h sh) $ zip ai barr
    h :: SPull Pos -> (Pos3,Pos) -> Program Pos3
    h sh (ai,b) = do
      seqFoldP ai sh $ \ai' c -> do
        ai'' <- calcA b c ai'
        return ai''


tn0 = printAnalysis (nbody0.zipp4) (inputPos :- ())
tn1 = printAnalysis (nbody1.zipp4) (inputPos :- ())

-- [(Par,Block,0),(Par,Thread,256)]
-- [(Par,Thread,4),(Seq,Thread,0)]

