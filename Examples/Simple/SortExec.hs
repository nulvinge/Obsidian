{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Examples.Simple.SortExec where

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
import Data.Word

-- import Examples.Simple.Scan


{-
perform =
  withCUDA $
  do
    kern <- capture (256, 0) (sklansky 10 (+) . splitUp 1024) 

    useVector (V.fromList [0..1023 :: Word32]) $ \i -> 
      allocaVector 1024 $ \ (o :: CUDAVector Word32) ->
      do
        fill o 0
        o <== (1,kern) <> i 
        r <- peekCUDAVector o
        lift $ putStrLn $ show r 
-}

perform = do
  tt <- getCurrentTime
  withCUDA False $ do

    tt <- lift $ printTimeSince "init cuda" tt

    let size = 1024*1024
        inputSI :: SPull EInt32
        inputSI = namedGlobal "apa" size

    let il = [0..(fromIntegral size-1)]
    useVector (V.fromList il) $ \i ->
      allocaVector (fromIntegral size) $ \ (o :: CUDAVector Int32) -> do
        fill o 0
        lift $ printTimeSince "create vectors" tt
        sequence_ [runKern inputSI i o s | s <- [5..9]]

runKern input i o bs = do
  let size = len input
  tt <- lift $ getCurrentTime
  
  kern <- captureWithStrategy
        [(Par,Block,0),(Par,Thread,2^bs),(Seq,Thread,0)]
        ((pConcatMapJoin $ liftM push . bitonicSort1) . splitUpS (2^bs))
        (input :- ())
  sync
  tt <- lift $ printTimeSince "init" tt

  o <== kern <> i
  sync
  tt <- lift $ printTimeSince "run once" tt

  r <- peekCUDAVector o
  sync
  lift $ printTimeSince "readback" tt
  let ss :: Int32
      ss = fromIntegral size
      sumil = ss*(ss+1)`div`2
  --lift $ putStrLn $ show r
  --lift $ putStrLn $ show $ sum $ P.take (fromIntegral bs) il
  lift $ putStrLn $ show $ sum r
  lift $ putStrLn $ show $ sumil
  lift $ putStrLn $ "diff " ++ (show $ sumil + sum r)
  fill o 0
  sync

  tt <- lift $ getCurrentTime
  sequence_ $ P.replicate 1000 $ do
    o <== kern <> i
    sync
  lift $ printTimeSinceN 1000 (2*fromIntegral size) tt $ "bench\tsort"
    ++ "\t" ++ show size
    ++ "\t" ++ show bs 
    ++ "\t" ++ show (2^bs)
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

