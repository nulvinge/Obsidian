{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.Dependency.Hazards
  (insertEdges
  ,keepHazards
  ,makeFlowDepEdges
  ,eliminateIndependent
  ,unneccessarySyncs
  ,Direction (..)
  ,DepEdgeType (..)
  ,DepEdge
  )  where

import Obsidian.Dependency.Helpers
import Obsidian.Dependency.Range
import Control.DeepSeq
import Data.List as L
import qualified Data.Map as M

listProduct :: [a] -> [b] -> [(a,b)]
listProduct la lb = [(a,b) | a <- la, b <- lb]
combinations :: [a] -> [(a,a)]
combinations l = concat $ map (\(i,ll) -> map (i,) ll) $ zip l (prefixes l)
prefixes :: [a] -> [[a]]
prefixes l = map (`L.take` l) $ L.take (length l) [0..]


updateDependence :: Access -> Access -> [(Direction,(Exp Word32,Bool))] -> [(Direction,(Exp Word32,Bool))]
updateDependence aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) t
  | liftM2 rangeIntersect (getRange ad a) (getRange bd b) == Just False = []
  | gcdTest (a-b)       = []
  | any ((==DNone).fst) t2 = []
  | otherwise = t2
    where (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba
          t2 = map testFunctions t
          testFunctions a@(d,(e,ps)) = (,(e,ps))
                                     $ intersectionsD
                                     $ catMaybes
                                     -- $ trace (show (ai,bi))
                                     -- $ strace
                                     $ map (\f -> f a)
                                     $ funcs
          funcs :: [(Direction, (Exp Word32, Bool)) -> Maybe Direction]
          funcs =
            [Just . fst
            , \(d,l) -> guard (sameGroup $ fst l)     >> return DEqual
            , \_     -> guard same                    >> return DNEqual
            , \_     -> guard diffBits                >> return DNone
            -- , \(d,l) -> (lookup l sameBits) >>= guard >> return DEqual
            ]

          mds = aa `diffs` ba
          (d0,ds) = fromJust mds
          sameGroup e = isJust mds && d0 == 0 &&
                      (  (af == bf && af /= 0)
                      || (getRange ad e == Just (0,0)))
            where (_,af,bf) = fromMaybe (undefined,0,0) $ lookup e ds
          (diffBits,sameBits) = bitTests aa ba $ map snd t

isIndependent :: Access -> Access -> Bool
isIndependent aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi)
  | an /= bn            = True --different arrays
  | arw && brw          = True --read read
  -- -- | isJust d && fromJust d /= 0 = True --banerjee
  -- | liftM2 rangeIntersect (getRange ad a) (getRange bd b) == Just False = True
  | same && sameTBGroup = True
  -- slowest tests last
  -- | gcdTest (a-b)       = True
  | banerjee aa ba      = True
  | fst $ bitTests aa ba (getLoops ad) = True
  | otherwise           = False
      where (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba
            sameTBGroup = sameThread && (local || sameBlock)

sameWarp :: Access -> Access -> Bool
sameWarp aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi)
  -- | ad `sameWarpRange` bd && rangeSize (warprange ad) <= 32 = trace (show (ai,bi,a,b,warprange ad,warprange bd,getRange ad (ThreadIdx X),getRange bd (ThreadIdx X))) True
  | otherwise = False --needs better analysis
  where
    sameWarpRange d1 d2 = mapPair2 (==) (warprange d1) (warprange d2) == (True,True)
    warprange d = mapPair (*warpsize) (tl `div` warpsize, (th+1)`cdiv`warpsize)
      where Just (tl,th) = getRange d (ThreadIdx X)

rangeSize (l,h) = h-l

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
         ,map (\((e,sp,a),(_,_,b)) -> (e,(sp,a,b))) $ zip afs bfs)

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
         -> (Name, Exp Word32, Bool, IMData, (Int,Int))
         -> [(Exp Word32,Bool)]
         -> (Bool, [((Exp Word32,Bool),Bool)])
bitTests aa@(an,a,arw,ad,ai) ba@(bn,b,brw,bd,bi) loops = -- trace (show (ai,bi)) $
  bitTests' a b (getRange ad) (getRange bd) loops

--( +  ( *  blockIdx.x 1024 ) ( |  ( &  threadIdx.x 511 ) ( <<  ( &  threadIdx.x 4294966784 ) 1 ) ) )
testBitTest = undefined -- bitTests' True True h h gr gr
  where t = ThreadIdx X
        bt = BlockIdx X
        i = 1
        a = (t .&. complement i)
        b = a <<* 1
        c = (t .&. i) .|. b
        d = (t .&. i) .|. (b `xor` i+1)
        e = bt * 256 + t
        f = (t .&. 1) .|. ((t .&. 4294967294) <<* 1)
        h = 128*t+128 + (4294967295)
        gr (ThreadIdx X) = Just (0,511)
        gr (Literal a) = Just (fromIntegral a,fromIntegral a)
        gr _ = Nothing

type Bit a = Either (Bool,(Int,Exp a)) (Maybe Bool)

instance (Scalar a) => NFData (Exp a) where
  rnf e = traverseExp (\a -> a`seq`a) e `seq` ()

bitTests' a b grad grbd loops = -- strace $ trace (show (same,local,varIdBits (ThreadIdx X),varIdBits (BlockIdx X),a,b,varBits)) $
    (or knownBits
    ,map (\(e,ps) -> ((e,ps),sameCheck e)) loops)
  where
    sameCheck i = case (grad i) of
      Just (_,ir) -> possibleBits ir == (varIdBits i)
      Nothing     -> let (t,i') = Prelude.last varBits --not wholy safe
        in if i /= i'
          then False
          else 2^(t+1)-1 == (varIdBits i)
    varIdBits i = foldr (.|.) 0
                $ map (bit.fst)
                $ filter ((==i).snd) varBits

    (varBits,knownBits) = partitionEithers
                        $ map final
                        $ zip (getBits grad a) (getBits grbd b)
    final ab = case ab of
        (Right (Just False),b) -> isGood b
        (Right (Just True), b) -> isGood $ notB b
        (a,Right (Just False)) -> isGood a
        (a,Right (Just True))  -> isGood $ notB a
        (Left (True,a),Left (False,b)) | a==b -> Right True
        (Left (False,a),Left (True,b)) | a==b -> Right True
        (Left fa@(_,a), Left fb@(_,b)) |fa==fb-> Left a
        (a,b) | a==b           -> Right False
        _                      -> Right False
    isGood a = Right $ a == Right (Just True)

    getBits :: (Exp Word32 -> Maybe (Integer,Integer)) -> Exp Word32 -> [Bit Word32]
    getBits d a = case d a of
      Just (l,h) | l==h      -> map (Right . Just) $ makeBits l
      Just (l,h)             -> map (findCandidate a)
                              $ zip3 (getBits' d a) [0..]
                              $ makeBits
                              $ possibleBits h
      _                      -> map (findCandidate a)
                              $ zip3 (getBits' d a) [0..]
                              $ map (const True) [0..31]

    findCandidate a (r,t,False) = -- if r == Right (Just False) || r == Right Nothing then Right $ Just False else trace (show ("fc",a,r,t)) $
      Right $ Just False
    findCandidate a (Right Nothing,t,_) = (Left (False,(t,a)))
    findCandidate a (r,_,_) = r
    makeBits a = map (testBit a) [0..31]

    getBits' :: (Bits a, Num a, Ord a, Scalar a) => (Exp Word32 -> Maybe (Integer,Integer)) -> Exp a -> [Bit a]
    getBits' d (BinOp Sub a b) =
      rec d (a+((complement b)+1))
    getBits' d (BinOp Mul a (Literal b)) | is2Power b =
      rec d (a <<* fromIntegral (log2 b))
    getBits' d (BinOp Mul (Literal a) b) | is2Power a =
      rec d (b <<* fromIntegral (log2 a))
    getBits' d (BinOp Div a (Literal b)) | is2Power b =
      rec d (a >>* fromIntegral (log2 b))
    getBits' d (BinOp ShiftL a (Literal b)) =
          L.take (bitSize a)
        $ L.replicate b (Right $ Just False)
       ++ rec d a
    getBits' d (BinOp ShiftR a (Literal b)) =
          L.take (bitSize a)
        $ rec d a
       ++ L.replicate b (Right $ Just False)
    getBits' d e@(BinOp bop a b) = (a',b') `deepseq`
        map (\t -> getBitVal t bop a' b') [0..bitSize e-1]
      where a' = (rec d a)
            b' = (rec d b)
    getBits' d (UnOp BitwiseNeg a) = map notB $ rec d a
    getBits' d a = L.replicate (bitSize a) $ Right Nothing

    rec :: (Scalar a) => (Exp Word32 -> Maybe (Integer,Integer)) -> Exp a -> [Bit a]
    rec d a = c -- trace (show ("testtest",a,L.take 4 c)) c 
      where c = rec' (witness a) a
            rec' Word32Witness x = getBits d x
            rec' _             _ = L.replicate 32 $ Right Nothing --weird default

    getBitVal :: (Scalar a, Scalar b, Scalar c, Bits c)
              => Int -> Op ((a,b) -> c) -> [Bit a] -> [Bit b] -> Bit c
    getBitVal t _ _ _ | t < 0 = Right $ Just False
    getBitVal t _ _ _ | t >= 32 = Right $ Just False
    getBitVal t BitwiseAnd a b =
      case (a!!t,b!!t) of
        (Right (Just True),b)  -> b
        (a,Right (Just True))  -> a
        (Right (Just False),b) -> Right $ Just False
        (a,Right (Just False)) -> Right $ Just False
        (a,b) | a==b           -> a
        (Left (True,a),Left (False,b)) | a==b -> Right $ Just False
        (Left (False,a),Left (True,b)) | a==b -> Right $ Just False
        _                      -> Right Nothing
    getBitVal t BitwiseOr a b = -- trace (show (a,b,(getBitVal t d a,getBitVal t d b))) $ strace $
      case (a!!t,b!!t) of
        (Right (Just False),b) -> b
        (a,Right (Just False)) -> a
        (Right (Just True),b)  -> Right $ Just True
        (a,Right (Just True))  -> Right $ Just True
        (a,b) | a==b           -> a
        (Left (True,a),Left (False,b)) | a==b -> Right $ Just True
        (Left (False,a),Left (True,b)) | a==b -> Right $ Just True
        _                      -> Right Nothing
    getBitVal t BitwiseXor a b =
      case (a!!t,b!!t) of
        (Right (Just False),b) -> b
        (Right (Just True), b) -> notB b
        (a,Right (Just False)) -> a
        (a,Right (Just True))  -> notB a
        (a,b) | a==b           -> Right $ Just False
        (Left (True,a),Left (False,b)) | a==b -> Right $ Just True
        (Left (False,a),Left (True,b)) | a==b -> Right $ Just True
        _                      -> Right Nothing
    getBitVal t Add a b = -- strace $ trace (show (getBitVal (t-1) d (a .|. b),getBitVal (t-1) d (a .&. b),getCarry (t-1), sum)) $
      case getCarry (t-1) a b of
        Just False -> sum
        Just True  -> notB sum
        _          -> Right Nothing
        where sum = getBitVal t BitwiseXor a b
              getCarry :: (Scalar a, Bits a)
                       => Int -> [Bit a] -> [Bit a] -> Maybe Bool
              getCarry t a b
                -- | bor  == Right (Just False) = (Just False)
                | band == Right (Just True)  = Just True
                | bxor == Right (Just False) = Just False
                | bxor == Right (Just True)  = getCarry (t-1) a b
                | getCarry (t-1) a b == Just False
                  && isLeft bxor             = Just False
                | otherwise                  = Nothing
                where bor  = getBitVal t BitwiseOr  a b
                      band = getBitVal t BitwiseAnd a b
                      bxor = getBitVal t BitwiseXor a b
    getBitVal t _ _ _ = Right Nothing

    findBit t a | t<0 = Right False
    findBit t a | t>= length a = Right False
    findBit t a = a !! t

    --log2 x = (\y -> y-1) $ Data.List.last $ takeWhile (not . testBit x) $ Prelude.reverse [0..bitSize x-1]
    log2 n = length (takeWhile (<n) (iterate (*2) 1))
    possibleBits x = getNext2Powerm (1+fromIntegral x :: Word32)

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
                 | DataAnyDep
  deriving (Show,Eq)

data Direction = DAny | DEqual | DNEqual | DLess | DMore | DELess | DEMore | DNone
  deriving (Show,Eq)

intersectionsD :: [Direction] -> Direction
intersectionsD = foldl intersectD DAny

intersectD :: Direction -> Direction -> Direction
intersectD DAny x          = x
intersectD x DAny          = x
intersectD DNone _         = DNone
intersectD _ DNone         = DNone
intersectD a b | a == b = a
intersectD a b | isJust $ intersectD' a b = fromJust $ intersectD' a b
intersectD a b | isJust $ intersectD' b a = fromJust $ intersectD' b a
intersectD' DEqual  DNEqual = Just DNone
intersectD' DEqual  DLess   = Just DNone
intersectD' DEqual  DMore   = Just DNone
intersectD' DEqual  DELess  = Just DEqual
intersectD' DEqual  DEMore  = Just DEqual
intersectD' DNEqual DLess   = Just DLess
intersectD' DNEqual DMore   = Just DMore
intersectD' DNEqual DELess  = Just DLess
intersectD' DNEqual DEMore  = Just DMore
intersectD' DLess   DMore   = Just DNone
intersectD' DLess   DELess  = Just DLess
intersectD' DLess   DEMore  = Just DNone
intersectD' DMore   DELess  = Just DNone
intersectD' DMore   DEMore  = Just DMore
intersectD' DELess  DEMore  = Just DEqual
intersectD' _ _ = Nothing

--thid does not handle synchronization within loops yet
makeFlowDepEdges :: IMList IMData -> [DepEdge]
makeFlowDepEdges im
    = map (\((a,b,c),t) -> (a,b,t,c))
    $ M.toList 
    $ M.fromListWith (++)
    $ map (\(a,b,t,c)->((a,b,c),t))
    $ nub
    $ (\(_,(_,_,globs,a)) -> processGlobals globs ++ a)
    $ traverseIMaccDataPrePost pre post ([],[],[],[])
    $ im
  where
    pre :: ((Statement IMData, IMData), ([Access], [Access], [Access], [DepEdge]))
        -> (IMData, ([Access], [Access], [Access], [DepEdge]))
    pre ((SSynchronize, d),(loc,prevloc,glob,edges)) = (d,([],prevloc++loc,glob,edges))
    pre ((p,d),            (loc,prevloc,glob,edges)) = (d,
        (loc++local,prevloc,glob++global,edges++newedges))
      where (local,global) = partition (isLocal . \(n,_,_,_,_)->n) $ getAccessesIM (p,d)
            newedges = concat $ [makeEdges [] True True  (a,b) | a <- local, b <- prevloc]
                             ++ [makeEdges [] True False (a,b) | a <- local, b <- loc]
                             ++ [makeEdges [] True False (a,a) | a <- local]
                             ++ [makeEdges [] True False (a,b) | (a,b) <- combinations local]
    post ((p, d),(loc,prevloc,glob,edges)) = (d,(loc,prevloc,glob,edges))
    processGlobals gs = concat $ [makeEdges [] False False (a,b) | (a,b) <- combinations gs]
                              ++ [makeEdges [] True False (a,a) | a <- gs]
    memories = M.fromList $ collectIM c im
      where c (SAllocate n s t,d) = [(n,(s,t,d))]
            c _ = []
    getLoopsBelow n d
      -- | "arr"    `isPrefixOf` n = ThreadIdx X
      | "input"  `isPrefixOf` n = getLoops d
      | "output" `isPrefixOf` n = getLoops d
      | otherwise = getBelow (getLoops d) (getLoops md)
          where (_,_,md) = fromJust $ M.lookup n memories
                getBelow (a:as) (b:bs) | a == b = getBelow as bs
                getBelow as [] = as

    makeEdges :: [Exp Bool] -> Bool -> Bool -> (Access,Access) -> [DepEdge]
    makeEdges conds local nosync (aa@(an,a,arw,ad,ai),ba@(bn,b,brw,bd,bi))
      | an /= bn   = [] --different arrays
      | arw && brw = [] --read read
      | otherwise  = [(ai, bi, loops, conds)]
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
            loops = if getLoopsBelow an ad == getLoopsBelow bn bd
                      then [DataDep $ map (DAny,) $ getLoopsBelow an ad]
                      else [DataAnyDep]


eliminateIndependent :: M.Map (Int,Int) Access -> [DepEdge] -> [DepEdge]
eliminateIndependent accesses edges = catMaybes $ map tryEdge edges
  where
    tryEdge :: DepEdge -> Maybe DepEdge
    tryEdge (a',b',t,c) =
        if tf == [] -- || isIndependent aa ba
          then Nothing
          else Just (a',b',tf,c)
      where aa@(an,a,arw,ad,ai) = fromJust $ M.lookup a' accesses
            ba@(bn,b,brw,bd,bi) = fromJust $ M.lookup b' accesses
            tf = t2' ++ (mapMaybe (fmap DataDep
                                  .mfilter (/=[])
                                  .Just
                                  .updateDependence aa ba)
                        t')
            (t',t2') = partitionMaybes getDataDep t
            getDataDep (DataDep l) = Just l
            getDataDep _           = Nothing



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


unneccessarySyncs :: [Int] -> M.Map (Int,Int) Access -> [DepEdge] -> (Statement IMData,IMData) -> [Maybe String]
unneccessarySyncs syncs accesses edges (SSynchronize,d) =
  if not $ any isNothing nessesaries
    then [Just $ (++"...")
               $ L.take (80-4-3-3)
               $ concat 
               $ catMaybes nessesaries]
    else []
  where
    nessesaries = map makesNeccessary edges
    i = getInstruction d
    makesNeccessary (a'@(ai',_),b'@(bi',_),t,c)
      | not $ ai' > i && bi' < i = Just $ "" -- show (ai,bi)
      | (not same && sameThread) =
          Just $ show ai' ++ " depends on " ++ show bi' ++ " within same thread "
          -- (ai',bi',mds,same,sameThread, aa `sameWarp` ba)
      | sameWarp =
          Just $ show ai' ++ " depends on " ++ show bi' ++ " within same warp "
      | otherSyncs /= [] = Just $ show ai' ++ " depends on " ++ show bi'
                        ++ " but syncs at " ++ show otherSyncs ++ " makes this unnessary "
      | otherwise = Nothing
      where aa@(an,a,arw,ad,ai) = fromJust $ M.lookup a' accesses
            ba@(bn,b,brw,bd,bi) = fromJust $ M.lookup b' accesses
            (local, same, sameThread, sameBlock, sameWarp) = whatSame aa ba
            otherSyncs = filter (\s -> s /= i && ai' > s && bi' < s) syncs
unneccessarySyncs _ _ _ _ = []



