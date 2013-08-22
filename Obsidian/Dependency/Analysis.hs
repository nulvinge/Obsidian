{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.Dependency.Analysis (insertAnalysis) where

import qualified Obsidian.CodeGen.Program as P
import Obsidian.CodeGen.InOut
import Obsidian.Dependency.ExpAnalysis
import Obsidian.Dependency.Helpers
import Obsidian.Dependency.Range
import Obsidian.Dependency.Coalesced
import Obsidian.Dependency.Cost
import Obsidian.Dependency.Hazards

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L

insertAnalysis :: Inputs -> ArraySizes -> IM -> IM
insertAnalysis ins inSizes im = traverseComment (map Just . getComments . snd) imF
                        -- ++ [(SComment (show $ M.assocs sizes),())]
                        ++ [(SComment "Depth:\t  Work:\tType:\tTotal cost:",())]
                        ++ map (\s -> (SComment s,())) (showCost cost)
                        ++ map (\s -> (SComment ("Hazard: " ++ show s),())) hazardEdges
                        -- ++ map (\s -> (SComment ("DepEdges: " ++ show s),())) depEdges1
                        ++ map (\s -> (SComment ("DepEdges: " ++ show s),())) depEdgesF
                        -- ++ map (\s -> (SComment ("Accesses: " ++ show s),())) (M.elems accesses)
                        -- ++ [(SComment $ show $ getOutputs im,())]
  where (inScalars,inConstSizes) = mapFst (map fst)
                                 $ partition ((==0).snd)
                                   [(n,l) | (n,Left l) <- inSizes]
        sizes = M.fromList $ inConstSizes ++ collectIM getSizesIM im0
        threadBudget = case numThreads im0 of
          Left tb -> fromIntegral tb
          Right tb -> tb

        outs = error $ show $ getOutputs im0

        im1, imF :: IMList IMData
        im0 = splitLoops defaultStrategy im
        (im1,depEdges1,_,_)            = runAnalysis threadBudget inScalars imActions1 im0
        (imF,depEdgesF,accesses,syncs) = runAnalysis threadBudget inScalars imActions2 $ emptyIM im1

        imActions1 :: [IMList IMData -> IMList IMData]
        imActions1 = [id
          , (\im -> trace (printIM (mapDataIM (const ()) im)) im)
          , moveLoops
          , mergeLoops
          , loopUnroll 4
          , cleanupAssignments
          , removeUnusedAllocations --move after scalar lifting
          , insertSyncs
          -- , (\im -> trace (printIM (emptyIM im)) im)
          ]

        imActions2 :: [IMList IMData -> IMList IMData]
        imActions2 = [id
          , insertStringsIM "Out-of-bounds" $ map (inRange sizes).getIndicesIM
          , insertStringsCostIM "Coalesce"  $ map isCoalesced.getIndicesIM
          , insertStringsIM "Diverging"     $ diverges
          , insertStringsIM "Instruction"   $ (:[]) . liftM show . mfilter (>=0) . Just . getInstruction . snd
          -- , insertStringsIM "Hazards"       $ insertEdges accesses hazardEdges
          , insertStringsIM "Unnessary sync"$ unneccessarySyncs syncs accesses depEdgesF
          , mapIMData insertCost
          -- , scalarLifting depEdgesF
          -- , insertStringsIM "Cost"    $ \(p,d) -> if getCost d /= noCost then [Just $ showCost (getCost d)] else []
          -- , insertStringsIM "Uppers" $ \(p,d) -> [Just $ show (M.toList $ getUpperMap d)]
          -- , insertStringsIM "Factors" $ \(p,d) -> [Just $ show (getLoops d)]
          ]

        cost = sumCost $ collectIM (list.getCost.snd) imF
        hazardEdges = keepHazards accesses depEdgesF

runAnalysis threadBudget inScalars actions im = (imF,depEdges,accesses,syncs)
  where
    im1, im2, imF :: IMList IMData
    im1 = mapDataIM (collectIMData.snd) $ insertIMCollection threadBudget inScalars im
    (im2,instructions) = traverseIMaccDataPre instructionNumbering [] im1
    imF = foldr (.) id (Prelude.reverse actions) im2
    accesses = M.fromList
            $ map (\a@(_,_,_,_,i) -> (i,a))
            $ concat
            $ map getAccessesIM instructions
    depEdges = eliminateIndependent accesses $ makeFlowDepEdges im2
    syncs = mapMaybe isSync instructions
    isSync (SSynchronize,d) = Just $ getInstruction d
    isSync _                = Nothing

emptyIM :: IMList a -> IMList ()
emptyIM = mapDataIM (const ())


insertStringsIM :: String -> ((Statement IMData, IMData) -> [Maybe String])
                -> IMList IMData -> IMList IMData
insertStringsIM s f = mapIMData g
  where g (statement,d) = addComments d $ map ((s++": ")++) $ catMaybes $ f (statement,d)
                               

insertStringsCostIM :: String
                    -> ((Statement IMData, IMData) -> [(CostT, Maybe String)])
                    -> IMList IMData -> IMList IMData
insertStringsCostIM s f = mapIMData g
  where g (statement,d0) = d2
          where (costs,strings) = unzip $ f (statement,d0)
                d1 = addIMCostT d0 (sumCostT costs)
                d2 = addComments d1 $ map ((s++": ")++) $ catMaybes $ strings



traverseComment :: ((Statement a,a) -> [Maybe String]) -> IMList a -> IMList ()
traverseComment f = mapDataIM (const ()) . traverseIM makeComment
  where makeComment a = map (\s -> (SComment s,undefined))
                            (catMaybes $ f a)
                    ++ [a]

{-
input1 :: DPull  EInt 
input1 = namedGlobal "apa" (variable "X")

t0 = printAnalysis (pushN 32 . fmap (+1). ixMap (+5)) (input1 :- ())
-}


-- Hazards

-- Memory

-- creating IMData

data IMDataCollection = CRange (Exp Word32) (Exp Word32, Exp Word32)
                      | CCond  (Exp Bool)
                      | CThreadConstant (Exp Word32) --more advanced analysis needed here
                      | CLoop LoopType (Exp Word32)

type Conds = [(Exp Bool)]

insertIMCollection :: EWord32 -> [Name] -> IMList a -> IMList (a,[IMDataCollection])
insertIMCollection bs inScalars = traverseIMaccDown (list `comp2` ins) start
  where
    ins :: [IMDataCollection] -> (Statement a,a) -> ((Statement a,(a,[IMDataCollection])),[IMDataCollection])
    ins cs b@(SCond          e l,a) = (mapSnd (,cs) b, cs ++ [CCond e])
    ins cs b@(SFor t pl nn   e l,a) = (mapSnd (,cs) b ,cs
                                   ++ collRange var e
                                   -- ++ [CThreadConstant (variable n)] -- not sure
                                   ++ [CLoop t var])
      where var = case (t,pl,nn) of
                    (Par,Thread,[])     -> ThreadIdx X
                    (Par,Block, [])     -> BlockIdx X
                    (_,_,nn) | nn /= [] -> variable nn
                    _                   -> error $ "Weird variable" ++ show (t,pl,nn)
    --ins cs b@(SSeqWhile     e l,a) = (mapSnd (,cs) b
    --                                 ,cs ++ [CCond e]
    --                                     ++ [CLoopSeq 2])
    ins cs b =                       (mapSnd (,cs) b,cs)

    start = collRange (ThreadIdx X) bs
         -- ++ [CLoopPar (ThreadIdx X)]
         ++ map (CThreadConstant . variable) inScalars
    collRange v e = [CRange v (0,e-1)]


collectIMData :: [IMDataCollection] -> IMData
collectIMData dc = IMDataA []
                           (M.fromListWith min $ catMaybes uppers)
                           (M.fromListWith max $ catMaybes lowers)
                           (S.fromList $ catMaybes $ map getBlockConsts dc)
                           noCost
                           loops
                           (-1)
  where
    getBlockConsts (CThreadConstant e) = Just e
    getBlockConsts _                   = Nothing

    loops = catMaybes $ map getLoopFactors dc
    getLoopFactors (CLoop Seq e) = Just $ (e,False)
    getLoopFactors (CLoop Par e) = Just $ (e,True)
    getLoopFactors _                  = Nothing

    (lowers,uppers) = unzip
                    $ map (\(e,(l,u)) -> (fmap (e,) l
                                         ,fmap (e,) u))
                    $ concat
                    $ map makeRange dc

    makeRange :: IMDataCollection -> [(Exp Word32, (Maybe Integer, Maybe Integer))]
    makeRange (CRange e (l,h)) = [(e, (expToMaybe $ Just l,expToMaybe $ Just h))]
    makeRange (CCond e) = map (\(e,(l,h)) -> (e,(l,h))) $ makeRangeE e
    makeRange _ = []


    makeRangeE :: Exp Bool -> [(Exp Word32, (Maybe Integer, Maybe Integer))]
    makeRangeE (BinOp o a b) = makeRangeB (witness a) o a b
    makeRangeE _ = []
    makeRangeB :: Witness a -> (Op ((a,b) -> Bool)) -> Exp a -> Exp b
               -> [(Exp Word32, (Maybe Integer, Maybe Integer))]
    makeRangeB Word32Witness Eq  a b = makeInEq (a-b)  $ \v -> (Just v, Just v)
    makeRangeB Word32Witness Lt  a b = makeInEq (a-b+1)$ \v -> (Nothing,Just v)
    makeRangeB Word32Witness LEq a b = makeInEq (a-b)  $ \v -> (Nothing,Just v)
    makeRangeB Word32Witness Gt  a b = makeInEq (a-b-1)$ \v -> (Just v,Nothing)
    makeRangeB Word32Witness GEq a b = makeInEq (a-b)  $ \v -> (Just v,Nothing)
    makeRangeB BoolWitness And a b = makeRangeE a ++ makeRangeE b
    makeRangeB _ _ _ _ = []

    minmax (a1,b1,c1) (a2,b2,c2) = (mergeMaybies max a1 a2, mergeMaybies min b1 b2, c1||c2)
    mergeMaybies f a b = case catMaybes [a,b] of
                          []    -> Nothing
                          [a]   -> Just a
                          [a,b] -> Just $ f a b
    maybeRange (Just a, Just b, s) = Just (a, b, s)
    maybeRange _                   = Nothing

    makeInEq :: Exp Word32
             -> (Exp Word32 -> (Maybe (Exp Word32), Maybe (Exp Word32)))
             -> [(Exp Word32, (Maybe Integer,Maybe Integer))]
    makeInEq a f = map solToRange $ solveIneq a
      where solToRange (var,val,left) =
              if left
                then (var,mapPair expToMaybe $        f val)
                else (var,mapPair expToMaybe $ swap $ f val)
    expToMaybe :: (Integral a) => Maybe (Exp a) -> Maybe Integer
    expToMaybe (Just (Literal a)) = Just $ fromIntegral a
    expToMaybe _                  = Nothing

    solveIneq :: Exp Word32 -> [(Exp Word32, Exp Word32, Bool)]
    solveIneq x = [(e, move p $ M.delete e m, p >= 0)
                  | (e,p) <- M.assocs m, p/=0, e/=1]
      where m = linerize x
            --solves p*e+a <> 0 => e <> -a/p
            move p a = (-(unLinerize a)) `div` fromIntegral (abs p)

instructionNumbering :: ((Statement IMData, IMData), [(Statement IMData,IMData)])
                     -> (IMData, [(Statement IMData,IMData)])
instructionNumbering ((p,d),il) =
  case shouldCount of
    Just p' -> let d' = setInstruction d (length il)
               in (d', il++[(p',d')])
    Nothing -> (d,il)
  where shouldCount :: Maybe (Statement IMData)
        shouldCount = case p of
            SAssign n l e -> Just $ SAssign n l e
            SSynchronize  -> Just SSynchronize
            _             -> Nothing


insertSyncs :: IMList IMData -> IMList IMData
insertSyncs = traverseIMaccDown trav architecture
  where
    trav :: [(LoopLocation, Integer)]
         -> (Statement IMData, IMData)
         -> [((Statement IMData, IMData), [(LoopLocation, Integer)])]
    trav ((loc,size):as) (SFor Par pl name n l,d)
      | tryLess n size && simplePL pl
      = ((SFor Par loc name n l,d),as)
      : if loc /= Thread then [] else [((SSynchronize,d),as)]
      where tryLess (Literal n) size = fromIntegral n <= size
            tryLess _ _ = True
            simplePL Unknown = True
            simplePL l = l == loc
    trav as p                      = [(p,as)]

type LoopInfo = (LoopType, LoopLocation, Name, EWord32, IMData)

moveLoops :: IMList IMData -> IMList IMData
moveLoops = traverseIMaccDown trav []
  where
    trav :: [LoopInfo] -> (Statement IMData,IMData) -> [((Statement IMData,IMData),[LoopInfo])]
    trav loops (SFor t pl name n l,d) | simpleL l
      = concat $ map (trav (loopInsert (t,pl,name,n,d) loops)) $ l
    trav loops (SFor t pl name n l0,d)
      = map (,[]) 
      $ foldr (\(t,l,name,n,d) li -> [(SFor t l name n li,d)]) l0
      $ L.reverse
      $ loopInsert (t,pl,name,n,d) loops
    trav [] (p,d) = [((p,d),[])]

    simpleL [(SFor _ _ _ _ _,_)] = True
    simpleL _ = False

    loopInsert :: LoopInfo -> [LoopInfo] -> [LoopInfo]
    loopInsert x [] = [x]
    loopInsert x (y:ys) | shouldMove x y && (simpleCanMove x y
                       || canMove (getDirection x) (getDirection y))
      = y : loopInsert x ys
      where
        shouldMove (_,l1,_,_,_)  (_,l2,_,_,_) = compare l1 l2 == LT
        -- insert advanced analysis
        getDirection (_,_,_,_,_) = DAny
        canMove DEqual DEqual = True
        canMove DEqual DLess  = True
        canMove DLess  DLess  = True
        canMove DLess  DEqual = True
        canMove DLess  DMore  = False
        canMove _      _      = False
        simpleCanMove (Par,_,_,_,_) (Par,_,_,_,_) = True
        simpleCanMove (Seq,_,_,_,_) (Par,_,_,_,_) = True
        simpleCanMove _             _             = False
    loopInsert x ys = x : ys

mergeLoops :: IMList IMData -> IMList IMData
mergeLoops = traverseIMaccDown trav []
  where
    trav :: [LoopInfo] -> (Statement IMData,IMData) -> [((Statement IMData,IMData),[LoopInfo])]
    trav loops (SFor Par pl name n l,d) | simpleL l
      = concat $ map (trav (loopInsert (Par,pl,name,n,d) loops)) l
    trav loops (SFor Par pl name n l0,d)
      = map (,[]) 
      $ foldr merge l0
      $ groupBy interchangeable
      $ L.reverse
      $ loopInsert (Par,pl,name,n,d) loops
    trav [] (p,d) = [((p,d),[])]

    interchangeable (Par,_,_,_,_) (Par,Unknown,_,_,_) = True
    -- interchangeable (Par,Unknown,_,_,_) (Par,_,_,_,_) = True
    interchangeable (Par,l1,_,_,_) (Par,l2,_,_,_)     = l1 == l2
    interchangeable a b = False

    simpleL [(SFor Par _ _ _ _,_)] = True
    simpleL _ = False

    loopInsert = (:)

    merge :: [LoopInfo] -> IMList IMData -> IMList IMData
    merge loops@((t,l,name,n,d):_) ll
      | length loops == 1 = [(SFor t l name n ll,d)]
      | otherwise         = [(SFor t l var size im,d)]
      where var = show l
            exp = variable var
            names :: [(Name,EWord32,EWord32,IMData)]
            (names,size) = foldr (\(_,_,name,n,d) (names,ns) -> ((name,ns,n,d):names,ns*n)) ([],1) loops
            im = concatMap makeAssign names ++ ll
            makeAssign (name,o,n,d) = [(SDeclare name Word32,d)
                                      ,(SAssign name [] e,d)]
              where e = if o*n == size
                          then exp`div`o
                          else (exp`div`o)`mod`n
    
    --(\(t,l,name,n,d) li -> [(SFor t l name n li,d)]) 

cleanupAssignments :: IMList IMData -> IMList IMData
cleanupAssignments = fst.traverseIMaccPrePost pre id []
  where
    pre ((SFor Par l name n ll,d),a) | isJust exp
      = ((SFor Par l [] n ll,d), (name,fromJust exp) : a)
      where exp = case l of
                    Thread -> Just $ ThreadIdx X
                    Block  -> Just $ BlockIdx  X
                    -- Just Vector -> Just $ variable "Vec"
                    _      -> Nothing
    pre ((SAssign name [] e,d),a) | simpleE (replace a e) && isJust e'
      = ((SComment "",d), (name,fromJust e') : a)
      where e' = witnessConv Word32Witness e
    pre ((p,d),a) = ((traverseExp (replace a) p,d),a)

    simpleE :: Exp a -> Bool
    simpleE (Index (n,[])) = True
    simpleE (ThreadIdx X)  = True
    simpleE (BlockIdx X)   = True
    simpleE (Literal n)    = True
    simpleE (BinOp op a (Literal b)) = simpleE a
    simpleE (BinOp op (Literal a) b) = simpleE b
    simpleE _              = False
    replace :: forall a. [(Name,Exp Word32)] -> Exp a -> Exp a
    replace m e@(Index (n,[])) = fromMaybe e $ witnessConv (witness e) =<< look n m
    replace m e = e
    look n m = liftM (traverseExp $ replace m) $ lookup n m

removeUnusedAllocations :: IMList IMData -> IMList IMData
removeUnusedAllocations im = mapIMs trav im
  where
    names = S.fromList $ collectIM getNamesIM im
    trav (SDeclare n _   ,_) | S.notMember n names = []
    trav (SAllocate n _ _,_) | S.notMember n names = []
    trav (SComment ""    ,_)                       = []
    trav (p,d) = [(p,d)]

scalarLifting :: [DepEdge] -> IMList IMData -> IMList IMData
scalarLifting depEdges = mapIMs liftAssigns
                       . mapIM liftReads
  where
    liftAssigns (SAssign n i e,d) | isJust liftable
        = (SAssign (fromJust liftable) [] e,d)
        : if hasOtherDependences d
            then [(SAssign n i $ getVar liftable $ e,d)]
            else []
      where liftable = getLiftable d
            getVar :: (Scalar a) => Maybe Name -> Exp a -> Exp a
            getVar (Just n) e = variable n
    liftAssigns (p,d) = [(p,d)]

    findSingle f l = case filter f l of
      [a] -> Just a
      _   -> Nothing
    hasOtherDependences d = not $ all (\(_,(bi,br),t,_) -> (getInstruction d == bi) `implies` isThreadDep t) depEdges
    implies True False = False
    implies _    _     = True
    getLiftable d = do
      _ <- getLift $ filter (\(_,(bi,br),_,_) -> getInstruction d == bi) depEdges
      return $ makeName $ getInstruction d

    getLift l = do
      guard $ all (\(_,_,t,_) -> isThreadDep t) l
      guard $ length l == 1
      let [a] = l
      return a
    isThreadDep t = all isThreadDep' t
    isThreadDep' DataAnyDep = False
    isThreadDep' SyncDepEdge = True
    isThreadDep' (DataDep ts) = all (\(d,(e,_)) -> if e == ThreadIdx X || e == BlockIdx X then d == DEqual else False) ts

    makeName i = "ts" ++ show i

    liftReads (p,d) = traverseExp (replaceExp replaceMap) (p,d)
      where replaceMap :: [(Exp Word32, Name, Name)]
            replaceMap = mapMaybe getLiftables $ getAccessesIM (p,d)
    getLiftables (n,e,r,d,i) = do
      guard r
      (_,(bi,br),_,_) <- getLift $ filter (\(a,_,_,_) -> i == a) depEdges
      return (e,n,makeName bi)
    replaceExp m (Index (n,[i])) =
      case find (\(e,n',_) -> n==n' && e==i) m of
        Just (_,_,liftName) -> variable liftName
        Nothing             -> Index (n,[i])
    replaceExp _ e = e


loopUnroll maxUnroll = mapIMs unroll
  where
    unroll (SFor Seq _ name (Literal s) ll,d) | s <= maxUnroll
      = (SDeclare name Word32,d)
      : concatMap (\i -> (SAssign name [] ((fromIntegral i) :: Exp Word32),d) : ll) [0..s-1]
    unroll (p,d) = [(p,d)]

splitLoops :: PreferredLoopLocation -> IM -> IM
splitLoops oldStrat im = traverseIMaccDown trav newStrat im
  where
    trav :: PreferredLoopLocation -> (Statement d,d) -> [((Statement d,d),PreferredLoopLocation)]
    trav strat (SFor Par Unknown name n ll,d) = map (,removeStrategy strat forFs) fors
      where 
        (fors,forFs) = splitLoop strat n f l0
        l0 e = (SDeclare name Word32,d)
             : (SAssign name [] e,d)
             : ll
        f (t,l,i,s) li lix = [(SFor t l var s (li ((t,l,s,variable var):lix)),d)]
          where var = name ++ "s" ++ show i
    trav strat (p@(SFor t l _ n ll),d) = [((p,d),removeStrategy' strat (t,l,n))]
    trav strat (SWithStrategy s p,d) = concat $ map (trav strat) p
    trav strat (p,d) = [((p,d),strat)]

    newStrat = makeStrat $ merge $ snd $ traverseIMaccUp collectLoops im
    makeStrat i = oldStrat

    collectLoops pl p@(SFor t l name n ll,d) = (p, Left (t,l,name,n) : merge pl)
    collectLoops pl p@(SWithStrategy s _ ,d) = (p, Right s : merge pl)
    collectLoops pl p = (p,merge pl)

    merge [] = []
    merge [a] = a
    merge t = foldr1 merge' t
    merge' a b = a

    addStrategy (a,b,pl) pl' = (a,b,pl++pl')
    getStrategy (a,b,pl) = pl
    removeStrategy :: PreferredLoopLocation -> [(LoopType,LoopLocation,EWord32)] -> PreferredLoopLocation
    removeStrategy pl pl' = foldr (flip removeStrategy') pl pl'
    removeStrategy' :: PreferredLoopLocation -> (LoopType,LoopLocation,EWord32) -> PreferredLoopLocation
    removeStrategy' [] _ = []
    removeStrategy' ((t,l,s):pl) (t',l',s'')
      | t == t' && l == l' && 1 == s' = pl
      | t == t' && l == l' && s == s' = pl
      | t == t' && l == l' && s <  s' = removeStrategy' pl (t',l',s''`div`fromIntegral s)
      | t == t' && l == l' && s >  s' = pl -- ((t,l,s`div`s'):pl)
      | otherwise = (t,l,s) : removeStrategy' pl (t',l',s'')
      where s' = fromInteger $ maxDivable s''

