{-# LANGUAGE ScopedTypeVariables,
             GADTs,
             RankNTypes,
             ExistentialQuantification,
             MultiParamTypeClasses,
             FlexibleInstances,
             TypeFamilies,
             TupleSections,
             FlexibleContexts #-}

module Obsidian.AddOn.Analysis.ExpAnalysis where

import Obsidian.Globs
import Obsidian
import qualified Obsidian.CodeGen.Program as P

import Data.Word
import Data.Int
import Data.Bits
import Data.Maybe
import Data.List
import Control.Monad.State

import Prelude hiding (zipWith,sum,replicate)
import qualified Prelude as P

instance Choice (TProgram ()) where  
  ifThenElse (Literal False) e1 e2 = e2
  ifThenElse (Literal True)  e1 e2 = e1
  ifThenElse b e1 e2 = do
    Cond b e1
    Cond (notE b) e2

{-
instance (MemoryOps a) => Choice (TProgram a) where  
  ifThenElse (Literal False) e1 e2 = e2
  ifThenElse (Literal True)  e1 e2 = e1
  ifThenElse b e1 e2 = do
    ns <- names (undefined :: a)
    allocateScalar ns 
    Cond b $ do
      v <- e1
      assignScalar ns v
    Cond (notE b) $ do
      v <- e1
      assignScalar ns v
    return (readFrom ns)
-}

getNext2Powerm :: Bits a => a -> a
getNext2Powerm v = if v == 0 then 0 else f (v-1) (bitSize v) 1
  where f v m n =
          if m < n
            then v
            else f (v .|. (v `shiftR` n)) m (n `shiftL` 1)

getNext2Power :: Bits a => a -> a
getNext2Power = (+1).getNext2Powerm

is2Power x = x .&. (x-1) == 0

{-

--simplifying treating i as an integer modulo m
simplifyMod :: Word32 -> Word32 -> Exp Word32 -> Exp Word32
simplifyMod m bs a' = (makeExp.(simplifyMod' m bs).snd.(simplifyMod' m bs)) a' --second time to get correct range after simplifications
  where makeExp :: (Maybe (Word32,Word32),Exp Word32) -> Exp Word32
        makeExp (Just (l,h),a) | l>=0 && h<m = a
        makeExp (_,a) = a`mod`(Literal m)
        {-
        makeExp (Just r,a) = error $ (show a) ++ " (originally " ++ (show a')
                          ++ ") not moddable by " ++ (show m)
                          ++ " because it has range " ++ show r
                          ++ " in size " ++ show bs
        makeExp (Nothing,a) = error $ (show a) ++ " not moddable by " ++ (show m) --a`mod`(Literal m)
        -}

--t0 = simplifyMod' 512 512 $ (ThreadIdx X)
--t1 = simplifyMod' 512 512 $ (ThreadIdx X) `div` 2
--t2 = simplifyMod' 512 512 $ (ThreadIdx X) `div` 2 *2
--t3 = simplifyMod' 512 512 $ (ThreadIdx X) `div` 2 *2*2
--t4 = simplifyMod' 32 16 $ (ThreadIdx X + 16)

simplifyMod' :: Word32 -> Word32 -> Exp Word32 -> (Maybe (Word32,Word32),Exp Word32)
simplifyMod' 0 bs = error "Divzero"
simplifyMod' m bs = sm
  where sm :: Exp Word32 -> (Maybe (Word32,Word32),Exp Word32)
        sm (Literal a) = (Just (am,am),Literal am)
            where am = a`mod`m
        sm (BinOp Mul a b) = after $ bop a b (*) (\al ah bl bh -> Just (al*bl,ah*bh))
        sm (BinOp Add a b) = bop a b (+) (\al ah bl bh -> Just (al+bl,ah+bh))
        sm (BinOp Sub a b) = bop a b (-) (\al ah bl bh -> Just (al-bh,ah-bl))
        sm (BinOp Div a b) = let (ab,av) = sm a in (ab,av `div` b)
        sm (BinOp Mod a bb@(Literal b)) = (Just (0,b-1),snd $ newmod b a (`mod`bb))
        sm (BinOp BitwiseXor a b) = bop a b xor (\al ah bl bh -> do
          guard $ al >= 0 && bl >= 0
          return (0,(getNext2Powerm ah `max` getNext2Powerm bh)))
        sm (ThreadIdx X) = (Just (0,bs-1),ThreadIdx X)
        sm a = (Nothing,a)
        bop :: Exp Word32 -> Exp Word32
            -> (Exp Word32 -> Exp Word32 -> Exp Word32)
            -> (Word32 -> Word32 -> Word32 -> Word32 -> Maybe (Word32,Word32))
            -> (Maybe (Word32,Word32),Exp Word32)
        bop a b f fw = (r,av `f` bv)
            where (ab,av) = sm a
                  (bb,bv) = sm b
                  r = do
                    (al,ah) <- ab
                    (bl,bh) <- bb
                    --guard $ al `fw` bl >= 0
                    --guard $ ah `fw` bh < m
                    fw al ah bl bh
        after :: (Maybe (Word32,Word32),Exp Word32) -> (Maybe (Word32,Word32),Exp Word32)
        after a@(_,(BinOp Mul _ (Literal 0)))  = a
        after a@(_,(BinOp Mul (Literal 0) _))  = a
        after (_,(BinOp Mul a b@(Literal bb))) = newmod (m`div`bb) a (*b)
        after (_,(BinOp Mul a@(Literal aa) b)) = newmod (m`div`aa) b (a*)
        --after (_,(BinOp Div a bb@(Literal b))) = newmod (m*b) a (`div`bb)
        --after (_,(BinOp Div aa@(Literal a) b)) = newmod (m*a) b (aa`div`)
        after a = a
        newmod :: Word32 -> Exp Word32
               -> (Exp Word32 -> Exp Word32)
               -> (Maybe (Word32,Word32),Exp Word32)
        newmod m' a f = (ab,f av)
            where (ab,av) = simplifyMod' m' bs a

simplifyDiv :: Word32 -> Word32 -> Word32 -> Exp Word32 -> Exp Word32
simplifyDiv m bs n = sd
  where sd :: Exp Word32 -> Exp Word32
        sd (Literal a) = Literal (a `div` m)
        sd (BinOp Mul a (Literal b)) = case gcd b m of
            d | d==b -> simplifyDiv (m`div`d) bs n a
            d | m==b -> simplifyDiv 1 bs n a
            d        -> ((fromIntegral (b`div`d)) * simplifyDiv 1 bs n a) `div` (fromIntegral (m`div`d))
        sd (BinOp Mul (Literal b) a) = sd (BinOp Mul a (Literal b))
        --sd (BinOp Mul a b) = error (show a ++ "*" ++ show b) -- sd a * b
        sd (BinOp Add a b) = sd a + sd b
        sd (BinOp Sub a b) = sd a - sd b
        sd (BinOp Div a (Literal b)) = simplifyDiv (m*b) bs n a
        sd (BinOp Div a b) = sd a `div` b
        sd (BinOp BitwiseXor a b) | is2Power m = sd a `xor` sd b
        sd (ThreadIdx X) | (min bs n) <= m = Literal 0
        sd (BlockIdx X)  | (n`div`bs) <= m = Literal 0
        sd a = a `div` Literal m

-}

{-
collectExp :: (Exp a -> b) -> (b -> b -> b) -> Exp a -> b
collectExp f g c@(BinOp Mul a b) = (collectExp f g a) `g` (collectExp f g b) `g` f c
collectExp f g c@(BinOp Add a b) = (collectExp f g a) `g` (collectExp f g b) `g` f c
collectExp f g c@(BinOp Sub a b) = (collectExp f g a) `g` (collectExp f g b) `g` f c
collectExp f g a = f a
-}


{-
traverseBin :: (Num (Exp a)) => (b -> Exp a -> (Exp a,b)) -> b -> Exp a -> Exp a 
            -> (Exp a -> Exp a -> Exp a) -> (Exp a,b)
traverseBin f d a b op = (lv `op` rv, rd)
    where (lv,ld) = traverseExp f d a
          (rv,rd) = traverseExp f ld b

traverseExp :: (Num (Exp a)) => (b -> Exp a -> (Exp a,b)) -> b -> Exp a -> (Exp a,b)
traverseExp f d (BinOp Mul a b) = traverseBin f d a b (*)
traverseExp f d (BinOp Add a b) = traverseBin f d a b (+)
traverseExp f d (BinOp Sub a b) = traverseBin f d a b (-)
traverseExp f d a = f d a
-}

class TraverseExp a where
  collectExp :: (forall e. Exp e -> [b]) -> a -> [b]
  traverseExp :: (forall e. Exp e -> Exp e) -> a -> a

instance (Scalar a) => TraverseExp (Exp a) where
  collectExp f e@(BinOp op a b) = f e ++ collectExp f a ++ collectExp f b
  collectExp f e@(UnOp op a)    = f e ++ collectExp f a
  collectExp f e@(If p a b)     = f e ++ collectExp f p ++ collectExp f a ++ collectExp f b
  collectExp f e@(Index (n,l))  = f e ++ concatMap (collectExp f) l
  collectExp f e = f e

  traverseExp f (BinOp Mul a b) = f $ (traverseExp f a) * (traverseExp f b)
  traverseExp f (BinOp Add a b) = f $ (traverseExp f a) + (traverseExp f b)
  traverseExp f (BinOp Sub a b) = f $ (traverseExp f a) - (traverseExp f b)
  traverseExp f (BinOp Div a b) = f $ (traverseExp f a) `div` (traverseExp f b)
  traverseExp f (BinOp op  a b) = f $ (BinOp op (traverseExp f a) (traverseExp f b))
  traverseExp f (UnOp  op  a)   = f $ (UnOp  op (traverseExp f a))
  traverseExp f (If p a b) = f $ If (traverseExp f p) (traverseExp f a) (traverseExp f b) 
  traverseExp f (Index (n,es)) = f $ Index (n,map (traverseExp f) es)
  traverseExp f a = f a

collectProg :: (forall e. Exp e -> [b]) -> TProgram a -> (a,[b])
collectProg f e@(Assign _ l a)= ((),  concatMap (collectExp f) l ++ collectExp f a)
collectProg f e@(Cond a b)    = let (v',b') = collectProg f b
                                in  (v', collectExp f a ++ b')
collectProg f e@(SeqFor n l)  = let (v',b') = collectProg f (l 0)
                                in  (v', collectExp f n ++ b')
collectProg f e@(Bind a g)    = let (v1,b1) = collectProg f a
                                    (v2,b2) = collectProg f (g v1)
                                in  (v2,b1 ++ b2)
collectProg f e@(Return a)    = (a,[])


collectAssign :: Names -> TProgram a -> (a,[Exp Word32])
collectAssign ns e@(Assign n [l] a) | n`inNames`ns = ((), [l])
                                    | otherwise    = ((), [])
collectAssign ns e@(Cond a b)  = collectAssign ns b
collectAssign ns e@(SeqFor n l)= collectAssign ns (l 0)
collectAssign ns e@(Bind a g)  = let (v1,b1) = collectAssign ns a
                                     (v2,b2) = collectAssign ns (g v1)
                                 in  (v2,b1 ++ b2)
collectAssign ns e@(Return a)  = (a,[])




instance TraverseExp (TProgram a) where
  collectExp = error "no collectExp for TProgram"

  traverseExp f (Assign n l a) = Assign n (map (traverseExp f) l) (traverseExp f a)
  traverseExp f (Cond a b) = Cond (traverseExp f a) (traverseExp f b)
  traverseExp f (SeqFor n l) = SeqFor (traverseExp f n) (\i -> traverseExp f (l i))
  traverseExp f (Bind a g) = Bind (traverseExp f a) (\b -> traverseExp f (g b))

--instance (TraverseExp a, TraverseExp b) => TraverseExp (a,b) where
--  collectExp f (a,b) = collectExp f a ++ collectExp f b
--  traverseExp f (a,b) = (traverseExp f a, traverseExp f b)


collectIM :: ((P.Statement a,a) -> [b]) -> P.IMList a -> [b]
collectIM f = concatMap (collectIM' f)
  where
    collectIM' f a@(P.SCond          _ l,_) = f a ++ collectIM f l
    collectIM' f a@(P.SSeqFor _      _ l,_) = f a ++ collectIM f l
    collectIM' f a@(P.SSeqWhile      _ l,_) = f a ++ collectIM f l
    collectIM' f a@(P.SForAll        _ l,_) = f a ++ collectIM f l
    collectIM' f a@(P.SForAllBlocks  _ l,_) = f a ++ collectIM f l
    collectIM' f a@(P.SForAllThreads _ l,_) = f a ++ collectIM f l
    collectIM' f a                      = f a

traverseIM :: ((P.Statement a,a) -> [(P.Statement a,c)]) -> P.IMList a -> P.IMList c
traverseIM f = traverseIMaccDown (\() l -> map (,()) $ f l) ()

{-
concatMap (traverseIM' f)
  where
    traverseIM' f (P.SCond           e l,a) = f $ (P.SCond          e (traverseIM f l),a)
    traverseIM' f (P.SSeqFor n       e l,a) = f $ (P.SSeqFor n      e (traverseIM f l),a)
    traverseIM' f (P.SSeqWhile       e l,a) = f $ (P.SSeqWhile      e (traverseIM f l),a)
    traverseIM' f (P.SForAll         e l,a) = f $ (P.SForAll        e (traverseIM f l),a)
    traverseIM' f (P.SForAllBlocks   e l,a) = f $ (P.SForAllBlocks  e (traverseIM f l),a)
    traverseIM' f (P.SForAllThreads  e l,a) = f $ (P.SForAllThreads e (traverseIM f l),a)
    traverseIM' f a = f a
-}

traverseIMaccDown :: (b -> (P.Statement a,a) -> [((P.Statement a,c),b)])
              -> b -> P.IMList a -> P.IMList c
traverseIMaccDown f acc = map g . concat . map (f acc)
  where
    g ((b,c),acc') = case b of
      (P.SCond           e l) -> (P.SCond          e (traverseIMaccDown f acc' l),c)
      (P.SSeqFor n       e l) -> (P.SSeqFor n      e (traverseIMaccDown f acc' l),c)
      (P.SSeqWhile       e l) -> (P.SSeqWhile      e (traverseIMaccDown f acc' l),c)
      (P.SForAll         e l) -> (P.SForAll        e (traverseIMaccDown f acc' l),c)
      (P.SForAllBlocks   e l) -> (P.SForAllBlocks  e (traverseIMaccDown f acc' l),c)
      (P.SForAllThreads  e l) -> (P.SForAllThreads e (traverseIMaccDown f acc' l),c)
      p                       -> (simpleIMmap p                                  ,c)

traverseIMaccUp :: ([b] -> (P.Statement c, a) -> ((P.Statement c, c), b))
                -> P.IMList a -> (P.IMList c, [b])
traverseIMaccUp f = unzip . map (g f)
  where
    g :: ([b] -> (P.Statement c, a) -> ((P.Statement c, c), b))
      -> (P.Statement a,a) -> ((P.Statement c,c) , b)
    g f (P.SCond           e l,a) = h f l $ \lt -> (P.SCond          e lt,a)
    g f (P.SSeqFor n       e l,a) = h f l $ \lt -> (P.SSeqFor n      e lt,a)
    g f (P.SSeqWhile       e l,a) = h f l $ \lt -> (P.SSeqWhile      e lt,a)
    g f (P.SForAll         e l,a) = h f l $ \lt -> (P.SForAll        e lt,a)
    g f (P.SForAllBlocks   e l,a) = h f l $ \lt -> (P.SForAllBlocks  e lt,a)
    g f (P.SForAllThreads  e l,a) = h f l $ \lt -> (P.SForAllThreads e lt,a)
    g f (p,a) = f [] (simpleIMmap p,a)
    --h :: [(P.Statement a, a)] -> ([(P.Statement c, c)], [b])
    h :: ([b] -> (P.Statement c, a) -> ((P.Statement c, c), b))
      -> P.IMList a
      -> (P.IMList c -> (P.Statement c, a))
      -> ((P.Statement c, c), b)
    h f l i = let (l',b)=unzip $ map (g f) l in f b (i l')

traverseIMaccPrePost :: (((P.Statement a,a),b) -> ((P.Statement a,c),b))
                     -> (((P.Statement d,c),b) -> ((P.Statement d,d),b))
                     -> b -> P.IMList a -> (P.IMList d,b)
traverseIMaccPrePost pre post b = swap . mapAccumL (curry $ swap . post . g (traverseIMaccPrePost pre post) . pre . swap) b
  where
    g :: (b -> P.IMList a -> (P.IMList d,b))
      -> ((P.Statement a,c),b) -> ((P.Statement d,c),b)
    g f ((P.SCond           e l,a),b) = h f b l $ \lt -> (P.SCond          e lt,a)
    g f ((P.SSeqFor n       e l,a),b) = h f b l $ \lt -> (P.SSeqFor n      e lt,a)
    g f ((P.SSeqWhile       e l,a),b) = h f b l $ \lt -> (P.SSeqWhile      e lt,a)
    g f ((P.SForAll         e l,a),b) = h f b l $ \lt -> (P.SForAll        e lt,a)
    g f ((P.SForAllBlocks   e l,a),b) = h f b l $ \lt -> (P.SForAllBlocks  e lt,a)
    g f ((P.SForAllThreads  e l,a),b) = h f b l $ \lt -> (P.SForAllThreads e lt,a)
    g f ((p,a),b) = ((simpleIMmap p,a),b)
    h :: (b -> P.IMList a -> (P.IMList d,b)) -> b -> P.IMList a
      -> (P.IMList d -> (P.Statement d,c)) -> ((P.Statement d,c),b)
    h f b l j = (j p',b')
      where (p', b') = f b l
    swap (a,b) = (b,a)

traverseIMaccDataPrePost pre post = traverseIMaccPrePost (f pre) (f post)
  where f g a@((p,_),_) = let (d',b') = g a in ((p,d'),b')

traverseIMaccDataPre pre = traverseIMaccPrePost (f pre) id
  where f g a@((p,_),_) = let (d',b') = g a in ((p,d'),b')

simpleIMmap :: P.Statement a -> P.Statement b
simpleIMmap (P.SAssign n l e      ) = (P.SAssign n l e      )
simpleIMmap (P.SAtomicOp n1 n2 e a) = (P.SAtomicOp n1 n2 e a)
simpleIMmap (P.SBreak             ) = (P.SBreak             )
simpleIMmap (P.SAllocate n s t    ) = (P.SAllocate n s t    )
simpleIMmap (P.SDeclare  n t      ) = (P.SDeclare  n t      )
simpleIMmap (P.SOutput   n t      ) = (P.SOutput   n t      )
simpleIMmap (P.SComment s         ) = (P.SComment s         )
simpleIMmap (P.SSynchronize       ) = (P.SSynchronize       )

instance TraverseExp a => TraverseExp [a] where
  collectExp f = concatMap (collectExp f)
  traverseExp f = map (traverseExp f)

instance TraverseExp (P.Statement a,a) where
  collectExp f = collectExp f . fst
  traverseExp f = mapFst $ traverseExp f
    where mapFst f (a,b) = (f a, b)

instance TraverseExp (P.Statement t) where
  collectExp f (P.SAssign _       l e) = collectExp f l ++ collectExp f e
  collectExp f (P.SAtomicOp _ _   e _) = collectExp f e
  collectExp f (P.SCond           e l) = collectExp f e ++ collectExp f l
  collectExp f (P.SSeqFor _       e l) = collectExp f e ++ collectExp f l
  collectExp f (P.SSeqWhile       e l) = collectExp f e ++ collectExp f l
  collectExp f (P.SForAll         e l) = collectExp f e ++ collectExp f l
  collectExp f (P.SForAllBlocks   e l) = collectExp f e ++ collectExp f l
  collectExp f (P.SForAllThreads  e l) = collectExp f e ++ collectExp f l
  collectExp f _ = []

  traverseExp f (P.SAssign n       l e) = P.SAssign n      (traverseExp f l) (traverseExp f e)
  traverseExp f (P.SAtomicOp n n2  e a) = P.SAtomicOp n n2 (traverseExp f e) a
  traverseExp f (P.SCond           e l) = P.SCond          (traverseExp f e) (traverseExp f l)
  traverseExp f (P.SSeqFor n       e l) = P.SSeqFor n      (traverseExp f e) (traverseExp f l)
  traverseExp f (P.SSeqWhile       e l) = P.SSeqWhile      (traverseExp f e) (traverseExp f l)
  traverseExp f (P.SForAll         e l) = P.SForAll        (traverseExp f e) (traverseExp f l)
  traverseExp f (P.SForAllBlocks   e l) = P.SForAllBlocks  (traverseExp f e) (traverseExp f l)
  traverseExp f (P.SForAllThreads  e l) = P.SForAllThreads (traverseExp f e) (traverseExp f l)
  traverseExp f a = a

getIndice :: Names -> Exp a -> [Exp Word32]
getIndice nn (Index (n,[r])) | n `inNames` nn = [r]
getIndice _ _ = []

getIndicesExp (Index (n,[r])) = [(n,r)]
getIndicesExp _ = []

getIndicesIM :: (P.Statement b, a) -> [(Name, Exp Word32, Bool, a)]
getIndicesIM (a,cs) = map (\(n,e,rw) -> (n,e,rw,cs)) $ getIndicesIM' a
  where
    getIndicesIM' :: (P.Statement b) -> [(Name, Exp Word32, Bool)]
    getIndicesIM' (P.SAssign     n [r] e) = [(n,r,False)] ++ ce r ++ ce e
    getIndicesIM' (P.SAssign     n r e)   = concat (map ce r) ++ ce e
    getIndicesIM' (P.SAtomicOp _ n r   _) = [(n,r,False)] ++ ce r
    getIndicesIM' (P.SCond           e l) = ce e
    getIndicesIM' (P.SSeqFor _       e l) = ce e
    getIndicesIM' (P.SSeqWhile       e l) = ce e
    getIndicesIM' (P.SForAll         e l) = ce e
    getIndicesIM' (P.SForAllBlocks   e l) = ce e
    getIndicesIM' (P.SForAllThreads  e l) = ce e
    getIndicesIM' _ = []
    ce :: (Scalar a) => (Exp a) -> [(Name, Exp Word32, Bool)]
    ce = map (\(n,e) -> (n,e,True)) . collectExp getIndicesExp

getSizesIM ((P.SAllocate n s t),_) = [(n,s)]
getSizesIM _ = []

traverseOnIndice :: Names -> (Exp Word32 -> Exp Word32) -> Exp a -> Exp a
traverseOnIndice nn f (Index (n,[r])) | n `inNames` nn = Index (n,[f r])
traverseOnIndice _ _ a = a


mapDataIM :: (a -> b) -> P.IMList a -> P.IMList b
mapDataIM f = traverseIMaccDown g ()
  where g () (a,b) = [((a, f b), ())]

mapIM :: ((P.Statement a,a) -> b) -> P.IMList a -> P.IMList b
mapIM f = traverseIMaccDown g ()
  where g () (a,b) = [((a, f (a,b)), ())]

