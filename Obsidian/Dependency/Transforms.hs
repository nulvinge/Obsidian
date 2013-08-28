{-# LANGUAGE GADTs,
             TypeFamilies,
             ScopedTypeVariables,
             FlexibleContexts,
             TupleSections,
             FlexibleInstances #-}

module Obsidian.Dependency.Transforms where

import Obsidian.Dependency.ExpAnalysis
import Obsidian.Dependency.Helpers
import Obsidian.Dependency.Range
import Obsidian.Dependency.Coalesced
import Obsidian.Dependency.Cost
import Obsidian.Dependency.Hazards

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L

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

splitLoops :: Strategy  -> IM -> IM
splitLoops oldStrat im = traverseIMaccDown trav newStrat im
  where
    trav :: Strategy  -> (Statement d,d) -> [((Statement d,d),Strategy)]
    trav strat (SFor Par Unknown name n ll,d) = map (,removeStrategy strat forFs) fors
      where 
        (fors,forFs) = splitLoop strat n f l0
        l0 e = (SDeclare name Word32,d)
             : (SAssign name [] e,d)
             : ll
        f (t,l,i,s) li lix = [(SFor t l var s (li ((t,l,s,variable var):lix)),d)]
          where var = name ++ "s" ++ show i
    trav strat (p@(SFor t l _ n ll),d) = [((p,d),removeStrategy' strat (t,l,n))]
    trav strat (p,d) = [((p,d),strat)]

    newStrat = makeStrat $ merge $ snd $ traverseIMaccUp collectLoops im
    makeStrat (n,p,s) = s2 ++ s3
      where s1 = strace $ splitLoopInfo oldStrat (p*s)
            s2 = map (\(t,l,s) -> (t,l,tryConst s)) s1
            s3 = removeStrategy oldStrat s1
            tryConst (Literal a) = a
            tryConst _ = 0


    collectLoops pl pr@(SFor Par l name nn ll,d) = (pr, (n+1,p*nn,s))
      where (n,p,s) = merge pl
    collectLoops pl pr@(SFor Seq l name nn ll,d) = (pr, (n+1,p,s*nn))
      where (n,p,s) = merge pl
    collectLoops pl pr = (pr,merge pl)

    merge [] = (0,1,1)
    merge [a] = a
    merge t = foldr1 merge' t
    merge' (n1,p1,s1) (n2,p2,s2) = (n1 `max` n2, p1 `maxE` p2, s1 `maxE` s2)

    addStrategy (a,b,pl) pl' = (a,b,pl++pl')
    getStrategy (a,b,pl) = pl
    removeStrategy :: Strategy -> [(LoopType,LoopLocation,EWord32)] -> Strategy
    removeStrategy pl pl' = foldr (flip removeStrategy') pl pl'
    removeStrategy' :: Strategy -> (LoopType,LoopLocation,EWord32) -> Strategy
    removeStrategy' [] _ = []
    removeStrategy' ((t,l,s):pl) (t',l',s'')
      | t == t' && l == l' && 1 == s' = pl
      | t == t' && l == l' && s == s' = pl
      | t == t' && l == l' && s <  s' = removeStrategy' pl (t',l',s''`div`fromIntegral s)
      | t == t' && l == l' && s >  s' = pl -- ((t,l,s`div`s'):pl)
      | otherwise = (t,l,s) : removeStrategy' pl (t',l',s'')
      where s' = fromInteger $ maxDivable s''

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
    pre ((SAssign name [] e,d),a) | simpleE (traverseExp (replace a) e) && isJust e'
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

scalarLiftingS :: M.Map (Int,Int) Access -> IMList IMData -> IMList IMData
scalarLiftingS accesses = mapIMs liftAssigns
                        . mapIM (traverseExp replaceExp)
  where
    arrmap = M.fromListWith (++)
           $ map (\(n,e,l,d,i) -> (n,[e]))
           $ M.elems accesses
    liftarrs = S.fromList
             $ map (\(n,es) -> n)
             $ filter (\(n,es) -> isSame es)
             $ M.toList arrmap
    isSame = all isSame'
    isSame' (ThreadIdx X) = True
    isSame' _ = False
    makeName n e = "ts" ++ n

    liftAssigns (SAssign n i e,d) | S.member n liftarrs =
                [(SAssign liftable [] e,d)]
        where liftable = makeName n e
    liftAssigns (p,d) = [(p,d)]

    replaceExp :: Exp e -> Exp e
    replaceExp (Index (n,[i])) | S.member n liftarrs =
               (variable $ makeName n i)
    replaceExp e = e
-- type Access = (Name, Exp Word32, Bool, IMData, (Int,Int))

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
    unroll (SFor Par Vector name (Literal s) ll,d) | s <= maxUnroll
      = (SDeclare name Word32,d)
      : concatMap (\i -> (SAssign name [] ((fromIntegral i) :: Exp Word32),d) : ll) [0..s-1]
    unroll (SFor Seq _ name (Literal s) ll,d) | s <= maxUnroll
      = (SDeclare name Word32,d)
      : concatMap (\i -> (SAssign name [] ((fromIntegral i) :: Exp Word32),d) : ll) [0..s-1]
    unroll (p,d) = [(p,d)]

