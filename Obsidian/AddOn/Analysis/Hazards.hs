{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.AddOn.Analysis.Hazards
  (insertEdges
  ,keepHazards
  ,makeFlowDepEdges
  ,eliminateIndependent
  ,unneccessarySyncs)  where

import qualified Obsidian.CodeGen.CUDA as CUDA
import qualified Obsidian.CodeGen.InOut as InOut
import Obsidian.CodeGen.Program
import Obsidian.Globs
import Obsidian
import Obsidian.AddOn.Analysis.ExpAnalysis
import Obsidian.AddOn.Analysis.Helpers
import Obsidian.AddOn.Analysis.Range

import Data.Word
import Data.Tuple
import Data.Int
import Data.List as L
import Data.Maybe
import Data.Either
import Data.Bits
import Control.Monad
import qualified Data.Map as M
import Debug.Trace

listProduct :: [a] -> [b] -> [(a,b)]
listProduct la lb = [(a,b) | a <- la, b <- lb]
combinations :: [a] -> [(a,a)]
combinations l = concat $ map (\(i,ll) -> map (i,) ll) $ zip l (prefixes l)
prefixes :: [a] -> [[a]]
prefixes l = map (`L.take` l) $ L.take (length l) [0..]

isIndependent :: Access -> Access -> Bool
isIndependent aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi)
  | an /= bn            = True --different arrays
  | arw && brw          = True --read read
  -- | isJust d && fromJust d /= 0 = True --banerjee
  | gcdTest (a-b)       = True
  | banerjee aa ba      = True
  | bitTests aa ba      = True
  | liftM2 rangeIntersect (getRange ad a) (getRange bd b) == Just False = True
  | same && sameTBGroup = True
  | otherwise           = False
      where (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba
            sameTBGroup = sameThread && (local || sameBlock)

sameWarp :: Access -> Access -> Bool
sameWarp aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi)
  | ad `sameWarpRange` bd && rangeSize (warprange ad) <= 32 = True
  | otherwise = False --needs better analysis

rangeSize (l,h) = h-l

warprange d = mapPair (*warpsize) (tl `div` warpsize, (th+1)`cdiv`warpsize)
  where Just (tl,th) = getRange d (ThreadIdx X)
sameWarpRange d1 d2 = mapPair2 (==) (warprange d1) (warprange d2) == (True,True)

whatSame aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi)
    = (local, same, sameThread, sameBlock, aa `sameWarp` ba)
  where mds = aa `diffs` ba
        (d0,ds) = fromJust mds
        sameThread = sameGroup (ThreadIdx X)
        sameBlock  = sameGroup (BlockIdx  X)
        sameTBGroup = sameThread && (local || sameBlock)
        sameGroup e = isJust mds && d0 == 0 &&
                    (  (af == bf && af /= 0)
                    || (getRange ad e == Just (0,0)))
          where (_,af,bf) = fromMaybe (undefined,0,0) $ lookup e ds
        local = isLocal an && isLocal bn
        same = ai == bi

--should be extended a lot
banerjee aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) = maybe False (0>) h
                                                || maybe False (>0) l
  where
    (al,ah) = getRangeM ad a
    (bl,bh) = getRangeM bd b
    (l,h) = (liftM2 (-) al bh,liftM2 (-) ah bl)

diffs aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) = do
  guard $ getLoops ad == getLoops bd
  (c0,afs,bfs) <- getFactors2 aa ba
  return (c0
         , map (\((e,sp,a),(_,_,b)) -> (e,(sp,a,b))) $ zip afs bfs)

getFactors2 :: Access -> Access -> Maybe (Integer, [(Exp Word32,Bool,Integer)], [(Exp Word32,Bool,Integer)])
getFactors2 aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) = do
    guard $ 0 == (M.size $ linerize $ unLinerizel a0v - unLinerizel b0v)
    return (a0-b0,af,bf)
  where (a0,af,a0v) = getFactors ad a
        (b0,bf,b0v) = getFactors bd b
        isConst e = getBlockConstant ad e && getBlockConstant bd e


getFactors :: IMData -> Exp Word32 -> (Integer, [(Exp Word32,Bool,Integer)], [(Exp Word32,Integer)])
getFactors d e = (sum consts, factors, nonLoopConst)
  where e' = linerize e
        factors = map (\(f,ps) -> (f,ps,M.findWithDefault 0 f e')) $ getLoops d
        (consts,nonconsts) = partitionMaybes (\(k,n) -> liftM (n*) $ getConst k)
                            $ M.toList e'
        nonLoopConst       = filter (\(k,_) -> not $ any ((==k).fst) $ getLoops d) nonconsts
        getConst a = do
          (l,h) <- getRange d a
          guard $ l==h
          Just l

gcdTest :: Exp Word32 -> Bool
gcdTest a =
  case signum d of
    0 -> False -- trace (show (a,factors,a0)) a0 /= 0
    1 -> a0 `mod` d /= 0
    -1 -> False --dont know
  where
    (lins,factors) = partition ((==1).fst) $ linerizel a
    a0 = case lins of [] -> 0; [(Literal 1,a)] -> -a
    d = if factors == [] then 0 else foldr1 gcd $ map snd factors


bitTests :: (Name, Exp Word32, Bool, IMData, (Int,Int))
         -> (Name, Exp Word32, Bool, IMData, (Int,Int)) -> Bool
bitTests aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) = -- trace (show (ai,bi)) $
  bitTests' same local a b (getRange ad) (getRange bd)
  where
    same = ai == bi
    local = isLocal an && isLocal bn

--( +  ( *  blockIdx.x 1024 ) ( |  ( &  threadIdx.x 511 ) ( <<  ( &  threadIdx.x 4294966784 ) 1 ) ) )
testBitTest = bitTests' True False e e gr gr
  where t = ThreadIdx X
        bt = BlockIdx X
        a = (t .&. complement 1)
        b = a <<* 1
        c = (t .&. 1) .|. b
        d = (t .&. 1) .|. t
        e = bt * 256 + t
        gr (ThreadIdx X) = Just (0,255)
        gr (Literal a) = Just (fromIntegral a,fromIntegral a)
        gr _ = Nothing

bitTests' same local a b grad grbd = -- strace $ trace (show (same,local,varIdBits (ThreadIdx X),varIdBits (BlockIdx X),a,b,varBits)) $
  if same
    then if local
      then sameCheck (ThreadIdx X)
      else sameCheck (ThreadIdx X) && sameCheck (BlockIdx X)
    else or knownBits
  where
    sameCheck i = case idRange i of
      Just ir -> getNext2Powerm ir == (varIdBits i)
      Nothing -> let (t,i') = Prelude.last varBits --not wholy safe
        in if i /= i'
          then False
          else 2^(t+1)-1 == (varIdBits i)
    varIdBits i = foldr (.|.) 0
                $ map (bit.fst)
                $ filter ((==i).snd) varBits
    idRange :: Exp Word32 -> Maybe Word32
    idRange = liftM (fromIntegral . snd) . grad
    (varBits,knownBits) = partitionEithers $ map bitTest [0..bitSize a-1]
    isGood a = Right $ a == Right (Just True)

    bitTest t = case (getBitVal t grad a,getBitVal t grbd b) of
        (Right (Just False),b) -> isGood b
        (Right (Just True), b) -> isGood $ notB b
        (a,Right (Just False)) -> isGood a
        (a,Right (Just True))  -> isGood $ notB a
        (Left (True,a),Left (False,b)) | a==b -> Right True
        (Left (False,a),Left (True,b)) | a==b -> Right True
        (Left (_,a), Left (_,b))       | a==b -> Left a
        (a,b) | a==b           -> Right False
        _                      -> Right False

    getBitVal :: Int -> (Exp Word32 -> Maybe (Integer,Integer)) -> Exp Word32 -> Either (Bool,(Int,Exp Word32)) (Maybe Bool)
    getBitVal t d _ | t < 0 = Right $ Just False
    getBitVal t d _ | t >= 32 = Right $ Just False
    getBitVal t d (BinOp BitwiseAnd a b) =
      case (getBitVal t d a,getBitVal t d b) of
        (Right (Just True),b)           -> b
        (a,Right (Just True))           -> a
        (Right (Just False),b)          -> Right $ Just False
        (a,Right (Just False))          -> Right $ Just False
        -- (Right (Just a),Right (Just b)) -> Right $ Just $ a && b
        (a,b) | a==b                    -> a
        (Left (True,a),Left (False,b)) | a==b -> Right $ Just False
        (Left (False,a),Left (True,b)) | a==b -> Right $ Just False
        _                               -> Right Nothing
    getBitVal t d (BinOp BitwiseOr a b) = -- trace (show (a,b,(getBitVal t d a,getBitVal t d b))) $ strace $
      case (getBitVal t d a,getBitVal t d b) of
        (Right (Just False),b)           -> b
        (a,Right (Just False))           -> a
        (Right (Just True),b)           -> Right $ Just True
        (a,Right (Just True))           -> Right $ Just True
        -- (Right (Just a),Right (Just b))  -> Right $ Just $ a && b
        (a,b) | a==b                     -> a
        (Left (True,a),Left (False,b)) | a==b -> Right $ Just True
        (Left (False,a),Left (True,b)) | a==b -> Right $ Just True
        _                                -> Right Nothing
    getBitVal t d (BinOp BitwiseXor a b) =
      case (getBitVal t d a,getBitVal t d b) of
        (Right (Just False),b) -> b
        (Right (Just True), b) -> notB b
        (a,Right (Just False)) -> a
        (a,Right (Just True))  -> notB a
        (a,b) | a==b           -> Right $ Just False
        (Left (True,a),Left (False,b)) | a==b -> Right $ Just True
        (Left (False,a),Left (True,b)) | a==b -> Right $ Just True
        _                      -> Right Nothing
    getBitVal t d (BinOp ShiftL a (Literal b)) = getBitVal (t-b) d a
    getBitVal t d (BinOp ShiftR a (Literal b)) = getBitVal (t+b) d a
    getBitVal t d (UnOp BitwiseNeg a) = notB $ getBitVal t d a
    getBitVal t d (BinOp Add a b) = -- strace $ trace (show (getBitVal (t-1) d (a .|. b),getBitVal (t-1) d (a .&. b),getCarry (t-1), sum)) $
      case getCarry (t-1) of
        Just False -> sum
        Just True  -> notB sum
        _          -> Right Nothing
        where sum = getBitVal t d (a .|. b)
              getCarry t | getBitVal t d (a .|. b) == Right (Just False) = (Just False)
              getCarry t | getBitVal t d (a .&. b) == Right (Just True)  = (Just True)
              getCarry t | getBitVal t d (a .|. b) == Right (Just True)  = getCarry (t-1)
              getCarry t | isLeft (getBitVal t d (a .|. b))              = getCarry (t-1)
              getCarry t = Nothing
    getBitVal t d (BinOp Sub a b) = getBitVal t d (a+((complement b)+1))
    getBitVal t d (BinOp Mul a (Literal b)) | is2Power b =
      getBitVal t d (a <<* fromIntegral (log2 b))
    getBitVal t d (BinOp Mul (Literal a) b) | is2Power a =
      getBitVal t d (b <<* fromIntegral (log2 a))
    getBitVal t d (BinOp Div a (Literal b)) | is2Power b =
      getBitVal t d (a >>* fromIntegral (log2 b))
    getBitVal t d a = case d a of
      Just (l,h) | l==h      -> Right $ Just $ testBit l t
      Just (l,h) | h < bit t -> Right $ Just $ False
      _                      -> Left (False,(t,a))

    --log2 x = (\y -> y-1) $ Data.List.last $ takeWhile (not . testBit x) $ Prelude.reverse [0..bitSize x-1]
    log2 n = length (takeWhile (<n) (iterate (*2) 1))

    notB a = case a of 
        Right (Just a) -> Right $ Just $ not a
        Left (a,e)     -> Left (not a,e)
        _              -> Right Nothing


type DepEdge = ((Int,Int),(Int,Int),[DepEdgeType], [Exp Bool])
data DepEdgeType = SyncDepEdge
                 | WarpDepEdge
                 | BlockDepEdge
                 | ThreadDepEdge
                 | DataDep [(Direction,(Exp Word32,Bool))]
  deriving (Show,Eq)

data Direction = DAny | DEqual | DLess | DMore
  deriving (Show,Eq)

--thid does not handle synchronization within loops yet
makeFlowDepEdges :: IMList IMData -> [DepEdge]
makeFlowDepEdges = map (\((a,b,c),t) -> (a,b,t,c))
                 . M.toList 
                 . M.fromListWith (++)
                 . map (\(a,b,t,c)->((a,b,c),t))
                 . nub
                 . (\(_,(_,_,globs,a)) -> processGlobals globs ++ a)
                 . traverseIMaccDataPrePost pre post ([],[],[],[])
  where
    pre :: ((Statement IMData, IMData), ([Access], [Access], [Access], [DepEdge]))
        -> (IMData, ([Access], [Access], [Access], [DepEdge]))
    pre ((SSynchronize, d),(loc,prevloc,glob,edges)) = (d,([],prevloc++loc,glob,edges))
    pre ((p,d),            (loc,prevloc,glob,edges)) = (d,
        (loc++local,prevloc,glob++global,edges++newedges))
      where (local,global) = partition (isLocal. \(n,_,_,_,_)->n) $ getAccessesIM (p,d)
            newedges = concat $ [makeEdges [] True True  (a,b) | a <- local, b <- prevloc]
                             ++ [makeEdges [] True False (a,b) | a <- local, b <- loc]
                             ++ [makeEdges [] True False (a,a) | a <- local]
                             ++ [makeEdges [] True False (a,b) | (a,b) <- combinations local]
    post ((p, d),(loc,prevloc,glob,edges)) = (d,(loc,prevloc,glob,edges))
    processGlobals gs = concat $ [makeEdges [] False False (a,b) | (a,b) <- combinations gs]
                              ++ [makeEdges [] True False (a,a) | a <- gs]

makeEdges :: [Exp Bool] -> Bool -> Bool -> (Access,Access) -> [DepEdge]
makeEdges conds local nosync (aa@(an,a,arw,ad,ai),ba@(bn,b,brw,bd,bi))
  | an /= bn   = [] --different arrays
  | arw && brw = [] --read read
  | otherwise  = [(ai, bi, [DataDep $ map (DAny,) $ getLoops ad], conds)]
       ++(if not (local && nosync) then []
            else [(ai, bi, [SyncDepEdge], conds)]
      {- )++(if not (sameThread && sameTBGroup) then []
            else [(ai, bi, [ThreadDepEdge], conds)]
      )++(if sameThread || not (aa `sameWarp` ba && not sameTBGroup) then []
            else [(ai, bi, [WarpDepEdge], conds)]
      )++(if not sameBlock then []
            else [(ai, bi, [BlockDepEdge], conds)]
      -}
      )
  where (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba

eliminateIndependent :: M.Map (Int,Int) Access -> [DepEdge] -> [DepEdge]
eliminateIndependent accesses edges = catMaybes $ map tryEdge edges
  where
    tryEdge (a',b',t,c) = if isIndependent aa ba
        then Nothing
        else Just (a',b',t,c)
      where aa@(an,a,arw,ad,ai) = fromJust $ M.lookup a' accesses
            ba@(bn,b,brw,bd,bi) = fromJust $ M.lookup b' accesses


keepHazards :: M.Map (Int,Int) Access -> [DepEdge] -> [DepEdge]
keepHazards accesses = filter (not.hazardFree)
  where
    hazardFree (a',b',t,c)
      | elem SyncDepEdge t && local = True
      | not same && (sameThread || sameWarp) = True
      | otherwise = False
      where aa@(an,a,arw,ad,ai) = fromJust $ M.lookup a' accesses
            ba@(bn,b,brw,bd,bi) = fromJust $ M.lookup b' accesses
            (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba

insertEdges :: M.Map (Int,Int) Access -> [DepEdge] -> (Statement IMData,IMData) -> [Maybe String]
insertEdges accesses edges (p,d) = map showEdge
                                 $ filter (\((i,_),_,_,_) -> i == getInstruction d)
                                 $ edges
  where
    showEdge (a',b',t,c) = Just $ show a' ++ " with " ++ show b' ++ loc sameThread 
      where aa = fromJust $ M.lookup a' accesses
            ba = fromJust $ M.lookup b' accesses
            (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba

            loc True         = ": same thread dependence"
            loc _ | sameWarp = ": same warp dependence"
            loc _            = ""


unneccessarySyncs :: M.Map (Int,Int) Access -> [DepEdge] -> (Statement IMData,IMData) -> [Maybe String]
unneccessarySyncs accesses edges (SSynchronize,d) =
  if not $ any isNothing nessesaries
    then [Just $ concat 
               $ catMaybes nessesaries]
    else []
  where
    nessesaries = map makesNeccessary edges
    i = getInstruction d
    makesNeccessary (a'@(ai',_),b'@(bi',_),t,c)
      | not $ ai' > i && bi' < i = Just ""
      | (not same && sameThread) =
          Just $ show ai' ++ " depends on " ++ show bi' ++ " within same thread "
          -- (ai',bi',mds,same,sameThread, aa `sameWarp` ba)
      | sameWarp =
          Just $ show ai' ++ " depends on " ++ show bi' ++ " within same warp "
      | otherwise = Nothing
      where aa@(an,a,arw,ad,ai) = fromJust $ M.lookup a' accesses
            ba@(bn,b,brw,bd,bi) = fromJust $ M.lookup b' accesses
            (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba
            otherSyncs = accesses
unneccessarySyncs _ _ _ = []



