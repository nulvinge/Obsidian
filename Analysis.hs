


-- Coalesced

collectIndices a = map (\(_,[r]) -> r) $ collectIndex a
  where collectIndex (Index r) = [r]
        collectIndex _ = []

linerize :: (Num a) => Exp a -> Map (Exp a) a
linerize = normalize . linerize'

linerize' :: (Num a) => Exp a -> [(a,Exp a)]
linerize' (Add a b) = linerize' a ++ linerize' b
linerize' (Mul (Literal a) b) = map [(n,v) -> (n*a,v)] $ linerize' b
linerize' (Mul a (Literal b)) = linerize' (Mul (Literal b) a)
linerize (Literal a) = (a, Literal 1)
linerize a@(ThreadIdx X) = (fromIntegral 1, ThreadIdx X)
linerize a@(BlockIdx X) = (fromIntegral 1, BlockIdx X)
linerize a = (1,a)

normalize = foldr Map.empty f
  where f m (n,v) = if m.has v
    then m.update v (n + (m ! v))
    else m.insert v n

isWarpConstant (Literal a) = True
isWarpConstant (ThreadIdx X) = False
isWarpConstant (BlockIdx X) = True



-- Hazards

-- Memory

--analyzeMemory :: GProgram () -> Int
--analyzeMemory p = 
--  let compiledP = compile p -- allocate memory

