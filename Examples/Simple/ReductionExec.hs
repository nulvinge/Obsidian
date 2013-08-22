{-# LANGUAGE ScopedTypeVariables #-}

module ReductionExec where

import Examples.Simple.Reduction

import Prelude hiding (replicate)
import Prelude as P


import Obsidian
import Obsidian.Run.CUDA.Exec
-- import Obsidian.Run.CUDA.SC

import qualified Data.Vector.Storable as V
import Control.Monad.State

import Data.Int

t :: (MemoryOps a,Num a) => DPull (SPull a) -> DPush a
t arr = Push 1 $ \wf ->
          forAll (len arr) $ \ix ->
            forAll 1 $ \ix ->
              wf ((+1) $ arr!0!0) 0

performSmall =
  withCUDA $
  do
    kern <- capture (t . splitUp 512) (input :- ())
    --kern <- capture (reduce (+) . splitUp 512) (input :- ())

    useVector (V.fromList [0..511 :: Int32]) $ \i ->
      useVector (V.fromList [0,0 :: Int32]) $ \ o ->
      do
        sync
        lift $ putStrLn "test"
        o <== (1,kern) <> i 
        sync
        lift $ putStrLn "test"
        r <- peekCUDAVector o
        sync
        lift $ putStrLn "test"
        lift $ putStrLn $ show r 




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

