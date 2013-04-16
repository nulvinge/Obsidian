{-# LANGUAGE ScopedTypeVariables,
             GADTs,
             RankNTypes,
             ExistentialQuantification,
             MultiParamTypeClasses,
             FlexibleInstances,
             TypeFamilies,
             FlexibleContexts #-}

module ExpAnalysis where

import qualified Obsidian.CodeGen.CUDA as CUDA

import Obsidian.Program hiding (Bind,Return)
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Array
import Obsidian.Library
import Obsidian.Force
import Obsidian.Atomic
import Obsidian.Globs
import Obsidian.Memory

import Debug.Trace

import Data.Word
import Data.Int
import Data.Bits
import Data.Maybe
import Data.List (genericIndex)

import qualified Data.Vector.Storable as V

import Control.Monad.State

import Prelude hiding (zipWith,sum,replicate)
import qualified Prelude as P


--simplifying treating i as an integer modulo m
simplifyMod :: Word32 -> Word32 -> Exp Word32 -> Exp Word32
simplifyMod m bs a' = (makeExp.(simplifyMod' m bs).snd.(simplifyMod' m bs)) a' --second time to get correct range after simplifications
  where makeExp :: (Maybe (Word32,Word32),Exp Word32) -> Exp Word32
        makeExp (Just (l,h),a) | l>=0 && h<m = a
        makeExp (_,a) = a`mod`(Literal m)
        makeExp (Just r,a) = error $ (show a) ++ " (originally " ++ (show a')
                          ++ ") not moddable by " ++ (show m)
                          ++ " because it has range " ++ show r
                          ++ " in size " ++ show bs
        makeExp (Nothing,a) = error $ (show a) ++ " not moddable by " ++ (show m) --a`mod`(Literal m)

t0 = simplifyMod' 512 512 $ (ThreadIdx X)
t1 = simplifyMod' 512 512 $ (ThreadIdx X) `div` 2
t2 = simplifyMod' 512 512 $ (ThreadIdx X) `div` 2 *2
t3 = simplifyMod' 512 512 $ (ThreadIdx X) `div` 2 *2*2
t4 = simplifyMod' 32 16 $ (ThreadIdx X + 16)

getNext2Powerm :: Bits a => a -> a
getNext2Powerm v = if v == 0 then 0 else f (v-1) (bitSize v) 1
  where f v m n =
          if m < n
            then v
            else f (v .|. (v `shiftR` n)) m (n `shiftL` 1)

getNext2Power :: Bits a => a -> a
getNext2Power = (+1).getNext2Powerm

is2Power x = x .&. (x-1) == 0

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

class (MemoryOps a) => TraverseExp a where
  collectExp :: (forall e. Exp e -> b) -> (b -> b -> b) -> a -> b
  traverseExp :: (forall e. Exp e -> Exp e) -> a -> a

instance (Scalar a) => TraverseExp (Exp a) where
  collectExp f c e@(BinOp op a b) = f e  `c` collectExp f c a `c` collectExp f c b
  collectExp f c e@(UnOp op a) = f e  `c` collectExp f c a
  collectExp f c e@(If p a b) = f e `c` collectExp f c p `c` collectExp f c a `c` collectExp f c b
  collectExp f c e@(Index (n,es)) = f e `c` foldr1 c (map (collectExp f c) es)
  collectExp f c e = f e

  traverseExp f (BinOp Mul a b) = f $ (traverseExp f a) * (traverseExp f b)
  traverseExp f (BinOp Add a b) = f $ (traverseExp f a) + (traverseExp f b)
  traverseExp f (BinOp Sub a b) = f $ (traverseExp f a) - (traverseExp f b)
  traverseExp f (BinOp Div a b) = f $ (traverseExp f a) `div` (traverseExp f b)
  traverseExp f (BinOp op  a b) = f $ (BinOp op (traverseExp f a) (traverseExp f b))
  traverseExp f (UnOp  op  a)   = f $ (UnOp  op (traverseExp f a))
  traverseExp f (If p a b) = f $ If (traverseExp f p) (traverseExp f a) (traverseExp f b) 
  traverseExp f (Index (n,es)) = f $ Index (n,map (traverseExp f) es)
  traverseExp f a = f a

instance (TraverseExp a, TraverseExp b) => TraverseExp (a,b) where
  collectExp f c (a,b) = collectExp f c a `c` collectExp f c b
  traverseExp f (a,b) = (traverseExp f a, traverseExp f b)


getIndice :: Names -> Exp a -> [Exp Word32]
getIndice nn (Index (n,[r])) | n `inNames` nn = [r]
getIndice _ _ = []

traverseOnIndice :: Names -> (Exp Word32 -> Exp Word32) -> Exp a -> Exp a
traverseOnIndice nn f (Index (n,[r])) | n `inNames` nn = Index (n,[f r])
traverseOnIndice _ _ a = a

