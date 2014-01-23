{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Examples.Simple.SAXPYExec where

import ExamplesNoCUDA

import Prelude hiding (replicate)
import Prelude as P


import Obsidian
import Obsidian.Run.CUDA.Exec
-- import Obsidian.Run.CUDA.SC

import qualified Data.Vector.Storable as V
import Control.Monad.State
import Data.Time.Clock

import Data.Int

t :: (MemoryOps a,Num a) => DPull (SPull a) -> DPush a
t arr = Push 1 $ \wf ->
          forAll (len arr) $ \ix ->
            forAll 1 $ \ix ->
              wf ((+1) $ arr!0!0) 0

t2 :: (MemoryOps a,Num a) => SPull (SPull a) -> SPush a
t2 = pConcat . fmap (push . fmap (+1))

perform = do
  tt <- getCurrentTime
  withCUDA False $ do
    --kern <- capture (t . splitUp 512) (input :- ())
    --kern <- capture (t2 . splitUp 512) (inputS :- ())
    --kern <- capture (reduce (+) . splitUp 512) (inputS :- ())

    tt <- lift $ printTimeSince "init cuda" tt

    let size = 1024*1024*8
        bs = 2048
        inputSI :: SPull EFloat
        inputSI = namedGlobal "apa" size

    let xl = [0..(fromIntegral size-1)]
        yl = [0..(fromIntegral size-1)]
        ol = P.replicate (fromIntegral size) 0
    useVector (V.fromList xl) $ \(x :: CUDAVector Float) ->
      useVector (V.fromList yl) $ \(y :: CUDAVector Float) ->
        allocaVector (fromIntegral size) $ \(o :: CUDAVector Float) -> do
          lift $ printTimeSince "create vectors" tt
          sequence_ [runKern inputSI x y o (2^s) | s <- [5..10]]

runKern input x y o bs = do
  let size = len input
  tt <- lift $ getCurrentTime
  
  kern <- captureWithStrategy [(Par,Thread,bs),(Seq,Thread,8),(Par,Block,0)]
        (saxpy1 bs 2)
        (input :- input :- ())
  let kernname = "saxpy6-8"
  sync
  tt <- lift $ printTimeSince "init" tt

  o <== kern <> x <> y
  sync
  tt <- lift $ printTimeSince "run once" tt

  r <- peekCUDAVector o
  sync
  lift $ printTimeSince "readback" tt
  let ss = fromIntegral size
      sumil = 3*ss*(ss+1)/2
  --lift $ putStrLn $ show r
  --lift $ putStrLn $ show $ sum $ P.take (fromIntegral bs) il
  --lift $ putStrLn $ show $ sum r
  --lift $ putStrLn $ show $ sum il
  --lift $ putStrLn $ "diff " ++ (show $ sumil - fromIntegral (sum r))

  tt <- lift $ getCurrentTime
  sequence_ $ P.replicate 1000 $ do
    o <== kern <> x <> y
    sync
  lift $ printTimeSinceN 1000 (2*fromIntegral size) tt $ "bench\t" ++ kernname
    ++ "\t" ++ show size
    ++ "\t" ++ show bs 
    ++ "\t" ++ show 0
    ++ "\t"
  return ()

printTimeSince s tt = do
  tt' <- getCurrentTime
  let time = diffUTCTime tt' tt
  putStrLn $ "Time for " ++ s ++ ":\t" ++ show time
  return tt'

makeTime = fromRational . toRational
printTimeSinceN n ss tt s = do
  tt' <- getCurrentTime
  let time = makeTime $ diffUTCTime tt' tt
  putStrLn $ s ++ show n
          ++ "\t" ++ show time
          ++ "\t" ++ show (time / (n*ss))
          ++ "\t" ++ show (n*ss / 1e9 / time)
  return tt'


-- performLarge =
--   withCUDA $
--   do
--     kern <- capture (reduce (+) . splitUp 256) 

--     useVector (V.fromList [0..65535 :: Int32]) $ \i ->
--       allocaVector 256  $ \(o :: CUDAVector Int32) ->
--         allocaVector 1  $ \(o2 :: CUDAVector Int32) -> 
--         do
          
--           o <== (256,kern) <> i
--           o2 <== (1,kern) <> o 

--           r <- peekCUDAVector o2
--           lift $ putStrLn $ show r 

