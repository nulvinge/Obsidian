
module Examples.Simple.Reduction where

import Obsidian

import Prelude hiding (zipWith)

reduceLocal :: MemoryOps a
               => (a -> a -> a)
               -> SPull a
               -> Program (SPush a)
reduceLocal f arr
  | len arr == 1 = return $ push arr
  | otherwise    =
    do
      let (a1,a2) = halve arr
      arr' <- unsafeForce $ zipWith f a1 a2
      reduceLocal f arr'

reduce :: MemoryOps a
          => (a -> a -> a)
          -> DPull (SPull a) -> DPush a
reduce f = pConcatMap $ pJoin . reduceLocal f 


input :: DPull EInt32
input = undefinedGlobal (variable "X")

getReduce = quickPrint (reduce (+) . splitUp 256) (input :- ())

