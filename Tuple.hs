{-# LANGUAGE FlexibleInstances,
             --FlexibleContexts
             UndecidableInstances,
             OverlappingInstances,
             TypeFamilies
             #-}

module Tuple (t1,t2,t3,t4) where

data Wrapper a = W a

class Count a where
    count :: a -> Int

instance (Eq a) => Count (Wrapper a) where
    count _ = 1

instance (Count a, Count b) => Count (a,b) where
    count (a,b) = count a + count b

class RecTup a where
    type RecTuple a
    fromRecTuple :: RecTuple a -> a
    toRecTuple   :: a -> RecTuple a

instance RecTup (a,b,c) where
    type RecTuple (a,b,c) = (a,(b,c))
    fromRecTuple (a,(b,c)) = (a,b,c)
    toRecTuple (a,b,c) = (a,(b,c))

instance (RecTup a, Count (RecTuple a)) => Count a where
    count = count.toRecTuple

t1 = count (W True)
t2 = count (W True,W True)
t3 = count (W True,(W True,W True))
t4 = count (W True,W True,W True)


