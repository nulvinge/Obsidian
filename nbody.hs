import Obsidian
import Obsidian.Dependency.Analysis
import Obsidian.Inplace

-- http://http.developer.nvidia.com/GPUGems3/gpugems3_ch31.html

inputSF :: SPull EFloat
inputSF = namedGlobal "apa" (1024*16)

calcA :: Pos -> Pos -> Pos
calcA pi pj = pi*pi+pj*pj

-- a i = G * sum $ map (\j-> m(j) * (p(j) - p(i)) / (d2(i,j) + e2) ^ (2/3))
-- d2 i j = (abs (p(j) - p(i))) ^ 2
-- e2 = e^2

type Pos = EFloat

nbody0 :: SPull Pos -> SPush Pos
nbody0 arr = Push (len arr) $ \wf -> do
  forAll (n`div`256) $ \ib -> do
    ns <- names (undefined :: Pos)
    forAll 256 $ \it -> do
      allocateScalar ns
      assignScalar ns (0 :: Pos)
    seqFor (n`div`256) $ \jb -> do
      sh <- force $ (!jb) $ splitUp 256 arr
      forAll 256 $ \it ->
        seqFor 256 $ \jt -> do
          let dai = calcA (arr ! (ib*256+it)) (sh ! jt)
          assignScalar ns $ (readFrom ns) + dai
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


nbody1 :: SPull Pos -> SPush Pos
nbody1 arr = pSplitMap (256 :: Word32) (pJoin . fmap push . f) arr
  where
    n=sizeConv $ len arr
    f barr = do
      seqFoldA (push $ Pull 256 (\i -> 0 :: Pos))
               (splitUp 256 arr) (g barr)
    g barr ai carr = pJoin $ do
      sh <- force carr
      return $ pConcatMap (singletonP . h ai sh) barr
    h ai sh b = do
      seqFoldP (0 :: Pos) sh $ \ai c -> do
        let dai = calcA b c
        return (ai + dai)


tn0 = printAnalysis nbody0 (inputSF :- ())
tn1 = printAnalysis nbody1 (inputSF :- ())

-- [(Par,Block,0),(Par,Thread,256)]
-- [(Par,Thread,4),(Seq,Thread,0)]

