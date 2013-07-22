{-# LANGUAGE ScopedTypeVariables #-}

module Data.VMultiSet where

import Data.Tuple
import Data.Maybe
import qualified Data.Vector as V
import Data.Vector (Vector)
import Prelude hiding (any,all,zipWith)

data MultiSet a = MS { unMS :: Vector Occur }

instance Show a => Show (MultiSet a) where
  show = show . unMS

type Occur = Int

-- any :: (Bounded a, Enum a) => MultiSet a -> (Occur -> Bool) -> Bool
any f = V.foldr' (\x d -> d || f x) False
all f = V.foldr' (\x d -> d && f x) True

null :: (Bounded a, Enum a) => MultiSet a -> Bool
null = all (==0) . unMS

size :: (Bounded a, Enum a) => MultiSet a -> Occur
size = V.foldr' (+) 0 . unMS

distinctSize :: (Bounded a, Enum a) => MultiSet a -> Occur
distinctSize = V.foldr' (\x d -> d + if x>0 then 1 else 0) 0 . unMS

member :: (Bounded a, Enum a) => a -> MultiSet a -> Bool
member a s = 0 /= occur a s

notMember :: (Bounded a, Enum a) => a -> MultiSet a -> Bool
notMember a s = 0 == occur a s

occur :: (Bounded a, Enum a) => a -> MultiSet a -> Occur
occur a s = (unMS s) V.! fromEnum a

isSubsetOf :: (Bounded a, Enum a) => MultiSet a -> MultiSet a -> Bool
isSubsetOf a b = all (\(x,y) -> x <= y) $ V.zip (unMS a) (unMS b)

isProperSubsetOf :: (Bounded a, Enum a) => MultiSet a -> MultiSet a -> Bool
isProperSubsetOf a b = all (\(x,y) -> x < y) $ V.zip (unMS a) (unMS b)

empty :: forall a. (Bounded a, Enum a) => MultiSet a
empty = MS $ V.replicate (1+fromEnum (maxBound :: a)) 0

singleton :: forall a. (Bounded a, Enum a) => a -> MultiSet a
singleton a = MS $ V.generate (1+fromEnum (maxBound :: a))
                              (\i -> if i == fromEnum a then 1 else 0)

insert :: (Bounded a, Enum a) => a -> MultiSet a -> MultiSet a
insert a = insertMany a 1

a // l = MS $ unMS a V.// l
zipWith f a b = MS $ V.zipWith f (unMS a) (unMS b)

insertMany :: (Bounded a, Enum a) => a -> Occur -> MultiSet a -> MultiSet a
insertMany a o m = m // [(fromEnum a,0)]
  where b = max 0 $ o + (unMS m) V.! fromEnum a

delete :: (Bounded a, Enum a) => a -> MultiSet a -> MultiSet a
delete a = insertMany a (-1)

deleteMany :: (Bounded a, Enum a) => a -> Occur -> MultiSet a -> MultiSet a
deleteMany a o = insertMany a (-o)

deleteAll :: (Bounded a, Enum a) => a -> MultiSet a -> MultiSet a
deleteAll a m = m // [(fromEnum a,0)]

union :: (Bounded a, Enum a) => MultiSet a -> MultiSet a -> MultiSet a
union = zipWith (+)

unions :: (Bounded a, Enum a) => [MultiSet a] -> MultiSet a
unions mss = foldl1 union mss

maxUnion :: (Bounded a, Enum a) => MultiSet a -> MultiSet a -> MultiSet a
maxUnion = zipWith max

difference :: (Bounded a, Enum a) => MultiSet a -> MultiSet a -> MultiSet a
difference = zipWith (\x y -> max 0 $ x - y)

intersection :: (Bounded a, Enum a) => MultiSet a -> MultiSet a -> MultiSet a
intersection = zipWith (\x y -> abs $ x - y)

filter :: (Bounded a, Enum a) => (a -> Bool) -> MultiSet a -> MultiSet a
filter p = MS . V.imap (\i x -> if p (toEnum i) then x else 0) . unMS

partition :: (Bounded a, Enum a) => (a -> Bool) -> MultiSet a -> (MultiSet a, MultiSet a)
partition p = pairMap MS . V.unzip . V.imap (\i x -> if p (toEnum i) then (x,0) else (0,x)) . unMS
  where pairMap f (a,b) = (f a, f b)

--map :: (Bounded a, Enum a) => (Ord a, Ord b) => (a -> b) -> MultiSet a -> MultiSet b

--mapMaybe :: (Bounded a, Enum a)  => (a -> Maybe b) -> MultiSet a -> MultiSet b

--mapEither :: (Bounded a, Enum a) => (a -> Either b c) -> MultiSet a -> (MultiSet b, MultiSet c)

--concatMap :: (Bounded a, Enum a) => (a -> [b]) -> MultiSet a -> MultiSet b

--unionsMap :: (Bounded a, Enum a) => (a -> MultiSet b) -> MultiSet a -> MultiSet b


--bind :: (Bounded a, Enum a) => MultiSet a -> (a -> MultiSet b) -> MultiSet b

--join :: (Bounded a, Enum a) => MultiSet (MultiSet a) -> MultiSet a

ifoldr f x m = V.ifoldr f x (unMS m)

fold :: (Bounded a, Enum a) => (a -> b -> b) -> b -> MultiSet a -> b
fold f = ifoldr (\i x b -> f (toEnum i) b)

foldOccur :: (Bounded a, Enum a) => (a -> Occur -> b -> b) -> b -> MultiSet a -> b
foldOccur f = ifoldr (\i x b -> f (toEnum i) x b)

elems :: (Bounded a, Enum a) => MultiSet a -> [a]
elems = concat . map (uncurry $ flip replicate) . toOccurList

distinctElems :: (Bounded a, Enum a) => MultiSet a -> [a]
distinctElems = map fst . toOccurList

toList :: (Bounded a, Enum a) => MultiSet a -> [a]
toList = distinctElems

fromList :: (Bounded a, Enum a) => [a] -> MultiSet a
fromList = unions . map singleton 

toOccurList :: (Bounded a, Enum a) => MultiSet a -> [(a, Occur)]
toOccurList = catMaybes . V.toList . V.imap (\i x -> if x > 0 then Just (toEnum i,x) else Nothing) . unMS

--fromDistinctOccurList :: (Bounded a, Enum a) => [(a, Occur)] -> MultiSet a
--fromDistinctOccurList l = empty V.// map (\(a,o) -> (fromEnum a,o)) l

mul a = MS . V.map (*fromIntegral a) . unMS

