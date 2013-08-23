{-# LANGUAGE GADTs, 
             TypeFamilies,           
             FlexibleContexts,
             FlexibleInstances, 
             UndecidableInstances,
             OverlappingInstances,
             RankNTypes #-} 

{- Joel Svensson 2012 -} 

module Obsidian.Exp 
       (module Obsidian.Exp,
        module Obsidian.DimSpec) where 



import Data.List
import Data.Word
import Data.Int
import Data.Bits

import qualified Foreign.Storable as Storable

import Obsidian.DimSpec

---------------------------------------------------------------------------
-- Obsidian imports
import Obsidian.Types
import Obsidian.Globs

import Obsidian.CodeGen.SPMDC

---------------------------------------------------------------------------
-- some synonyms
type Data a = Exp a 

type EInt    = Exp Int      
type EWord   = Exp Word

type EInt8   = Exp Int8
type EInt16  = Exp Int16
type EInt32  = Exp Int32
type EInt64  = Exp Int64

type EWord8  = Exp Word8   
type EWord16 = Exp Word16 
type EWord32  = Exp Word32 
type EWord64  = Exp Word64 

type EFloat  = Exp Float  
type EDouble = Exp Double 
type EBool   = Exp Bool    



---------------------------------------------------------------------------
-- Class Scalar. All the things we can handle code generation for 

class (Eq a, ExpToCExp a, Show a) => Scalar a where 
  sizeOf :: Exp a -> Int   --  
  typeOf :: Exp a -> Type  --   Good enough for me ... 
  witness :: Exp a -> Witness a
  witness a = NothingWitness

data Witness a where
  Word32Witness :: Witness Word32
  BoolWitness :: Witness Bool
  NothingWitness :: Witness a

witnessConv :: Scalar b => Witness a -> Exp b -> Maybe (Exp a)
witnessConv w b = f w (witness b) b
  where f :: Witness a -> Witness b -> Exp b -> Maybe (Exp a)
        f Word32Witness Word32Witness b = Just b
        f BoolWitness BoolWitness b = Just b
        f _ _ _ = Nothing

instance Scalar Bool where  
  sizeOf _ = Storable.sizeOf (undefined :: Int)
  typeOf _ = Bool 
  witness a = BoolWitness

instance Scalar Int where 
  sizeOf _ = Storable.sizeOf (undefined :: Int)
  typeOf _ = Int

instance Scalar Int8 where 
  sizeOf _ = 1
  typeOf _ = Int8

instance Scalar Int16 where 
  sizeOf _ = 2
  typeOf _ = Int16

instance Scalar Int32 where 
  sizeOf _ = 4
  typeOf _ = Int32

instance Scalar Int64 where 
  sizeOf _ = 8 
  typeOf _ = Int64
  
instance Scalar Float where
  sizeOf _ = Storable.sizeOf (undefined :: Float)
  typeOf _ = Float
  
instance Scalar Double where 
  sizeOf _ = 8 -- Storable.sizeOf (undefined :: Double) 
  typeOf _ = Double

instance Scalar Word where
  sizeOf _ = Storable.sizeOf (undefined :: Word) 
  typeOf _ = Word
  
instance Scalar Word8 where
  sizeOf _ = 1
  typeOf _ = Word8 

instance Scalar Word16 where 
  sizeOf _ = 2
  typeOf _ = Word16
  
instance Scalar Word32 where 
  sizeOf _ = 4 
  typeOf _ = Word32
  witness a = Word32Witness
  
instance Scalar Word64 where 
  sizeOf _ = 8 
  typeOf _ = Word64



---------------------------------------------------------------------------
-- Expressions 
data Exp a where
  Literal :: Scalar a 
             => a 
             -> Exp a 
  
  {- 
  Add more specific constructors for block,thread variables
   (these concepts excist in both OpenCL and CUDA 
    but are accessed differently so it could be a good 
    idea to add them as constructors here. These 
    can be translated into the CUDA/OpenCL specific 
    concept later in the codegeneration 
  -}
  WarpSize :: Exp Word32
  
  BlockDim :: DimSpec -> Exp Word32
  
  BlockIdx :: DimSpec 
              -> Exp Word32
  ThreadIdx :: DimSpec
               -> Exp Word32
    
  Index   :: Scalar a => 
             (Name,[Exp Word32]) 
             -> Exp a 
             
  If      :: Scalar a 
             => Exp Bool
             -> Exp a 
             -> Exp a 
             -> Exp a 
                          
  BinOp   :: (Scalar a,
              Scalar b, 
              Scalar c) 
             => Op ((a,b) -> c) 
             -> Exp a 
             -> Exp b 
             -> Exp c 
             
  UnOp    :: (Scalar a, 
              Scalar b)
             => Op (a -> b)            
             -> Exp a 
             -> Exp b 
             

  
---------------------------------------------------------------------------
-- Operations 
-- TODO: needs conversion operations.. (Int -> Word) etc. 
data Op a where 
  Add :: Num (Exp a) => Op ((a,a) -> a) 
  Sub :: Num (Exp a) => Op ((a,a) -> a) 
  Mul :: Num (Exp a) => Op ((a,a) -> a) 
  Div :: (Integral (Exp a), Integral a) => Op ((a,a) -> a) 
  
  Mod :: Integral a => Op ((a,a) -> a)
         
  -- Trig
  Sin :: Floating a => Op (a -> a) 
  Cos :: Floating a => Op (a -> a)
  
  -- Comparisons
  Eq  :: Ord a => Op ((a,a) -> Bool)
  NotEq :: Ord a => Op ((a,a) -> Bool) 
  Lt  :: Ord a => Op ((a,a) -> Bool) 
  LEq :: Ord a => Op ((a,a) -> Bool) 
  Gt  :: Ord a => Op ((a,a) -> Bool) 
  GEq :: Ord a => Op ((a,a) -> Bool) 
  
  -- Boolean 
  And :: Op ((Bool,Bool) -> Bool) 
  Or  :: Op ((Bool,Bool) -> Bool)

  Not :: Op (Bool -> Bool) 
  
  -- Bitwise 
  BitwiseAnd :: Bits a => Op ((a,a) -> a) 
  BitwiseOr  :: Bits a => Op ((a,a) -> a)
  BitwiseXor :: Bits a => Op ((a,a) -> a) 
  BitwiseNeg :: Bits a => Op (a -> a)

  -- I DO NOT EVEN KNOW WHAT THIS MEANS: work around it! 
  ShiftL     :: (Bits a) => Op ((a, Int) -> a)  
  ShiftR     :: (Bits a) => Op ((a, Int) -> a)  
  
  -- built-ins
  Min        :: Ord (Exp a) => Op ((a,a) -> a) 
  Max        :: Ord (Exp a) => Op ((a,a) -> a) 

  -- Floating (different CUDA functions for float and double, issue maybe?) 
  Exp :: Floating a => Op (a -> a) -- "expf" 
  Sqrt :: Floating a => Op (a -> a) -- "sqrtf" 
  --RSqrt :: Floating a => Op (a -> a) -- "rsqrtf"
  Log :: Floating a => Op (a -> a) -- "logf"
  Log2 :: Floating a => Op (a -> a) -- "log2f"
  Log10 :: Floating a => Op (a -> a) -- "log10f"
  Log1p :: Floating a => Op (a -> a) -- "log1pf"
  Expm1 :: Floating a => Op (a -> a) -- "expm1f"
  Pow :: Floating a => Op ((a, a) -> a) -- "powf"
  -- Floating Trig
  Tan :: Floating a => Op (a -> a) -- "tanf"
  ASin :: Floating a => Op (a -> a) -- "asinf"
  ATan :: Floating a => Op (a -> a) -- "atanf"
  ACos :: Floating a => Op (a -> a) -- "acosf"
  SinH :: Floating a => Op (a -> a) -- "sinhf"
  TanH :: Floating a => Op (a -> a) -- "tanhf"
  CosH :: Floating a => Op (a -> a) -- "coshf"
  ASinH :: Floating a => Op (a -> a) -- "asinhf" 
  ATanH :: Floating a => Op (a -> a) -- "atanhf"
  ACosH :: Floating a => Op (a -> a) -- "acoshf"
  -- There is no "div" in "Num" but it's already defined above. 
  FDiv :: Fractional a => Op ((a, a) -> a) 

  Int32ToWord32 :: Op (Int32 -> Word32)
  Word32ToInt32 :: Op (Word32 -> Int32)
  Word32ToFloat :: Op (Word32 -> Float)
  Word32ToWord8 :: Op (Word32 -> Word8) 
  

---------------------------------------------------------------------------
-- helpers 

variable name = Index (name,[])
index name ix = Index (name,[ix])

warpSize :: Exp Word32
warpSize = WarpSize

---------------------------------------------------------------------------
-- Collect array names

collectArrays :: Scalar a => Exp a -> [Name]
collectArrays (Literal _) = []
collectArrays (ThreadIdx _) = []
collectArrays (BlockIdx _) = [] 
collectArrays (Index (name,[])) = []
collectArrays (Index (name,_)) = [name]
collectArrays (BinOp _ e1 e2) = collectArrays e1 ++ collectArrays e2
collectArrays (UnOp  _ e) = collectArrays e
collectArrays (If b e1 e2) = collectArrays b ++ 
                             collectArrays e1 ++ 
                             collectArrays e2
-- collectArrays a = error $ show a

collectArrayIndexPairs :: Scalar a => Exp a -> [(Name,Exp Word32)]
collectArrayIndexPairs (Literal _) = []
collectArrayIndexPairs (Index (name,[])) = []
collectArrayIndexPairs (Index (name,[ix])) = [(name,ix)]
collectArrayIndexPairs (BinOp _ e1 e2) = collectArrayIndexPairs e1 ++ collectArrayIndexPairs e2
collectArrayIndexPairs (UnOp  _ e) = collectArrayIndexPairs e
collectArrayIndexPairs (If b e1 e2) = collectArrayIndexPairs b ++ 
                                      collectArrayIndexPairs e1 ++ 
                                      collectArrayIndexPairs e2


---------------------------------------------------------------------------
-- Typecasts
---------------------------------------------------------------------------

i32ToW32 = UnOp Int32ToWord32
w32ToI32 = UnOp Word32ToInt32

w32ToF = UnOp Word32ToFloat

w32ToW8 = UnOp Word32ToWord8


---------------------------------------------------------------------------
-- 
instance Scalar a => Show (Exp a) where 
  show = printExp 

-- Look this over. Do I really need a types expression data type ?
--  (No real need for a Exp GADT I think. Go back to keeping it simple!) 
instance (Eq a, Scalar a) => Eq (Exp a) where
  (==) a b = -- error $ "equality test between exps: " ++ show a ++ " " ++ show b --
    expToCExp a == expToCExp b
    -- Maybe not efficient! But simple.


---------------------------------------------------------------------------
-- INT Instances
---------------------------------------------------------------------------
-- Added new cases for literal 0 (2012/09/25)
instance (Scalar a, Num a, Bits a) => Bits (Exp a) where  
  (.&.) x (Literal 0) = Literal 0
  (.&.) (Literal 0) x = Literal 0 
  (.&.) (Literal a) (Literal b) = Literal (a .&. b) 
  (.&.) a b = BinOp BitwiseAnd a b
  (.|.) x (Literal 0) = x
  (.|.) (Literal 0) x = x
  (.|.) (Literal a) (Literal b) = Literal (a .|. b)
  (.|.) a b = BinOp BitwiseOr  a b
  xor (Literal a) (Literal b) = Literal (a `xor` b) 
  xor a (Literal 0) = a
  xor (Literal 0) b = b
  xor a b = BinOp BitwiseXor a b 
  
  --TODO: See that this is not breaking something (32/64 bit, CUDA/Haskell)
  complement (Literal i) = Literal (complement i)
  complement a = UnOp BitwiseNeg a

  shiftL (Literal j) i = Literal (j `shiftL` i) 
  shiftL a i = BinOp ShiftL a (fromIntegral i)
  shiftR (Literal j) i = Literal (j `shiftL` i)
  shiftR a i = BinOp ShiftR a (fromIntegral i)
  bitSize a  = sizeOf a * 8
  isSigned a = isSigned (valType a)
    where valType :: Exp a -> a
          valType = undefined

  bit  = Literal . bit
  testBit = error "testBit: is undefined for Exp Int"
  popCount = error "popCoint: is undefined for Exp Int"


---------------------------------------------------------------------------
-- Word32 Instances
---------------------------------------------------------------------------

-- adding special shift operators for when both inputs are 
-- runtime values (2013-01-08) 
(<<*) :: (Scalar a, Bits a) => Exp a -> Exp Int -> Exp a 
(<<*) a b = BinOp ShiftL a b 

(>>*) :: (Scalar a, Bits a) => Exp a -> Exp Int -> Exp a 
(>>*) a b = BinOp ShiftR a b 

instance (Scalar a,Fractional a) => Fractional (Exp a) where
  (/) (Literal a) (Literal b) = Literal (a/b)
  (/) a b = BinOp FDiv a b
  recip a = (Literal 1) / a
  fromRational a = Literal (fromRational a)

instance (Scalar a,Floating a) => Floating (Exp a) where
  pi = Literal pi
  exp a = UnOp Exp a
  sqrt a = UnOp Sqrt a
  log a = UnOp Log a
  (**) a b = BinOp Pow a b
  
  -- log_b(x) = log_e(x) / log_e(b)
  logBase (Literal 2) b = UnOp Log2 b
  logBase (Literal 10) b = UnOp Log10 b
  logBase a b = (UnOp Log b) / (UnOp Log a)
  
  sin (Literal 0) = Literal 0
  sin a = UnOp Sin a
  tan (Literal 0) = Literal 0
  tan a = UnOp Tan a
  cos (Literal 0) = Literal 1
  cos a = UnOp Cos a
  
  asin (Literal 0) = Literal 0
  asin a = UnOp ASin a
  atan (Literal 0) = Literal 0
  atan a = UnOp ATan a
  acos (Literal 1) = Literal 0
  acos a = UnOp ACos a
  
  sinh (Literal 0) = Literal 0
  sinh a = UnOp Sin a
  tanh (Literal 0) = Literal 0
  tanh a = UnOp Tan a
  cosh (Literal 0) = Literal 1
  cosh a = UnOp Cos a
  
  asinh a = UnOp ASinH a
  atanh a = UnOp ATanH a
  acosh a = UnOp ACosH a
  
  -- Y-Less's comment
  -- Don't second guess the CUDA compiler (or, more accurately, assume that
  -- other compilers have this).
  --(/) (Literal 1) (UnOp Sqrt b) = UnOp RSqrt b -- Optimisation.
  
---------------------------------------------------------------------------
-- Word8 Instances
---------------------------------------------------------------------------
instance (Scalar a ,Num a) => Num (Exp a) where 
  (+) a (Literal 0) = a
  (+) (Literal 0) a = a
  (+) (Literal a) (Literal b) = Literal (a+b)

  -- Added 15 Jan 2013
  (+) (BinOp Mul (BinOp Div x (Literal a)) (Literal b))
       (BinOp Mod y (Literal c))
        | x == y && a == b && b == c = x 
      -- This spots the kind of indexing that occurs from 
      --  converting a bix tix view to and from gix view
        
  -- Added 2 oct 2012
  (+) (BinOp Sub b (Literal a)) (Literal c) | a == c  = b 
  (+) (Literal b) (BinOp Sub a (Literal c)) | b == c  = a 
 
  (+) a b = BinOp Add a b  
  
  (-) a (Literal 0) = a 
  (-) (Literal a) (Literal b) = Literal (a - b) 
  (-) a b = BinOp Sub a b 
  
  (*) a (Literal 1) = a 
  (*) (Literal 1) a = a
  (*) _ (Literal 0) = Literal 0
  (*) (Literal 0) _ = Literal 0
  (*) (Literal a) (Literal b) = Literal (a*b) 
  (*) a b = BinOp Mul a b 

  signum = error "signum: not implemented for Exp a"
  abs = error "abs: not implemented for Exp a" 
  fromInteger a = Literal (fromInteger a) 
   
instance (Scalar a, Real a) => Real (Exp a) where 
  toRational = error "toRational: not implemented for Exp a" 
  

instance (Scalar a, Enum a) => Enum (Exp a) where
  toEnum = error "toEnum: not implemented for Exp a" 
  fromEnum = error "fromEnum: not implemented for Exp a" 

instance (Scalar a, Integral a) => Integral (Exp a) where
  mod a b@(Literal 0) = (BinOp Mod a b)
  mod a b@(Literal 1) = (Literal 0)
  mod (Literal a) (Literal b) = Literal (a `mod` b) 
  mod a b = BinOp Mod a b
  div _ (Literal 0) = error "Division by zero in expression" 
  div (Literal a) (Literal b) = Literal (a `div` b)
  div a b@(Literal 1) = a
  div a b = BinOp Div a b
  quotRem = error "quotRem: not implemented for Exp a" 
  toInteger a = error $ "toInteger: not implemented for Exp a " ++ show a
  
---------------------------------------------------------------------------
  
infix 4 ==*, /=*, <*, >*, >=*, <=* 

class OrdE a where
  (==*), (/=*), (<*), (<=*), (>*), (>=*) :: a -> a -> Exp Bool
  maxE,minE :: a -> a -> a


instance (Scalar a, Ord a) => OrdE (Exp a) where
  (==*) (Literal a) (Literal b) = Literal (a == b) 
  (==*) a b = BinOp Eq a b
  (/=*) (Literal a) (Literal b) = Literal (a /= b) 
  (/=*) a b = BinOp NotEq a b 
  (<*)  (Literal a) (Literal b) = Literal (a < b) 
  (<*)  a b = BinOp Lt a b
  (<=*) (Literal a) (Literal b) = Literal (a <= b) 
  (<=*) a b = BinOp LEq a b
  (>*)  (Literal a) (Literal b) = Literal (a > b) 
  (>*)  a b = BinOp Gt  a b
  (>=*) (Literal a) (Literal b) = Literal (a >= b) 
  (>=*) a b = BinOp GEq a b
  maxE (Literal a) (Literal b) = Literal (max a b)
  maxE a b = BinOp Max a b
  minE (Literal a) (Literal b) = Literal (min a b)
  minE a b = BinOp Min a b

instance (OrdE (Exp a), Scalar a) => Ord (Exp a) where
  compare a b = compare (show a) (show b) -- a little dangerous, but usefull for comparisons
  max = error "You should probably use maxE instead of max"
  min = error "You should probably use minE instead of min"

instance (OrdE a, Choice a, OrdE b, Choice b) => OrdE (a,b) where
  (==*) (a1,a2) (b1,b2) = (a1 ==* b1) &&* (a2 ==* b2)
  (/=*) (a1,a2) (b1,b2) = (a1 /=* b1) ||* (a2 /=* b2)
  (<*)  (a1,a2) (b1,b2) = (a1 <* b1) ||* (a1 ==* b1 &&* a2 <* b2)
  (<=*) (a1,a2) (b1,b2) = (a1 <* b1) ||* (a1 ==* b1 &&* a2 <=* b2)
  (>*)  (a1,a2) (b1,b2) = (a1 >* b1) ||* (a1 ==* b1 &&* a2 >* b2)
  (>=*) (a1,a2) (b1,b2) = (a1 >* b1) ||* (a1 ==* b1 &&* a2 >=* b2)
  maxE a b = ifThenElse (a <=* b) b a
  minE a b = ifThenElse (a <=* b) a b

instance (Scalar a, Ord a) => OrdE a where
  (==*) a b = Literal (a == b) 
  (/=*) a b = Literal (a /= b) 
  (<*)  a b = Literal (a < b) 
  (<=*) a b = Literal (a <= b) 
  (>*)  a b = Literal (a > b) 
  (>=*) a b = Literal (a >= b) 
  maxE  a b = max a b
  minE  a b = min a b


--instance (Ord a, Ord b, Scalar a, Scalar b) => Ord (Exp a, Exp b) where
--  max = maxE
--  min = minE

infixr 3 &&*
infixr 2 ||* 
(&&*), (||*) :: Exp Bool -> Exp Bool -> Exp Bool
(&&*) a b = BinOp And a b 
(||*) a b = BinOp Or a b 

notE = UnOp Not

---------------------------------------------------------------------------
-- Choice class
---------------------------------------------------------------------------
class Choice a where 
  ifThenElse :: Exp Bool -> a -> a -> a 

instance Scalar a => Choice (Exp a) where  
  ifThenElse (Literal False) e1 e2 = e2
  ifThenElse (Literal True)  e1 e2 = e1
  ifThenElse b e1 e2 = If b e1 e2
  
instance (Choice a, Choice b) => Choice (a,b) where
  ifThenElse b (e1,e1') (e2,e2') = (ifThenElse b e1 e2,
                                    ifThenElse b e1' e2') 
  
---------------------------------------------------------------------------
-- Print Expressions
---------------------------------------------------------------------------
  
printExp :: Scalar a => Exp a -> String
printExp (BlockIdx X) = "blockIdx.x"
printExp (ThreadIdx X) = "threadIdx.x"
printExp (BlockDim X)   = "blockDim.x"
printExp (Literal a) = show a 
printExp (Index (name,[])) = name
printExp (Index (name,es)) = 
  name ++ "[" ++ ((concat . intersperse "," . map printExp) es) ++ "]"
printExp (BinOp op e1 e2) = "(" ++ printOp op ++ " " ++  printExp e1 ++ " " ++ printExp e2 ++ " )"
printExp (UnOp  op e) = "(" ++ printOp op ++ " " ++ printExp e ++ " )"
printExp (If b e1 e2) = "(" ++ printExp b ++ " ? " ++ printExp e1 ++ " : " ++ printExp e2 ++ ")"


printOp :: Op a -> String
printOp Add = " + " 
printOp Sub = " - " 
printOp Mul = " * "
printOp Div = " / "
printOp Mod = " % "
printOp ShiftL = " << "
printOp ShiftR = " >> "

-- printOp If  = " if "

printOp Eq  = " == "
printOp NotEq = " /= " 
printOp Lt  = " < " 
printOp LEq = " <= " 
printOp Gt  = " > "
printOp GEq = " >= " 

printOp And = " && "
printOp Or  = " || " 
printOp Not = " ! " 

printOp Min = " Min "
printOp Max = " Max " 

printOp Sin = " Sin " 
printOp Cos = " Cos "

printOp Log = " Log "
printOp Exp = " Exp "
printOp Log1p = " Log1p "
printOp Expm1 = " Expm1 "

printOp BitwiseAnd = " & "
printOp BitwiseOr  = " | " 
printOp BitwiseXor = " ^ " 
printOp BitwiseNeg = " ~ "  

---------------------------------------------------------------------------
-- Turn expressions into backend-expressions
---------------------------------------------------------------------------
class ExpToCExp a where 
  expToCExp :: Exp a -> CExpr 


instance ExpToCExp Bool where 
  expToCExp (Literal True) = cLiteral (IntVal 1) CInt 
  expToCExp (Literal False) = cLiteral (IntVal 0) CInt
  expToCExp a = expToCExpGeneral a 

instance ExpToCExp Int where 
  expToCExp (Literal a) = cLiteral (IntVal a) CInt
  expToCExp a = expToCExpGeneral a  

instance ExpToCExp Int8 where 
  expToCExp (Literal a) = cLiteral (Int8Val a) CInt8
  expToCExp a = expToCExpGeneral a  

instance ExpToCExp Int16 where 
  expToCExp (Literal a) = cLiteral (Int16Val a) CInt16
  expToCExp a = expToCExpGeneral a  

instance ExpToCExp Int32 where 
  expToCExp (Literal a) = cLiteral (Int32Val a) CInt32
  expToCExp a = expToCExpGeneral a  

instance ExpToCExp Int64 where 
  expToCExp (Literal a) = cLiteral (Int64Val a) CInt64
  expToCExp a = expToCExpGeneral a  

instance ExpToCExp Float where 
  expToCExp (Literal a) = cLiteral (FloatVal a) CFloat
  expToCExp a = expToCExpGeneral a 

instance ExpToCExp Double where 
  expToCExp (Literal a) = cLiteral (DoubleVal a) CDouble
  expToCExp a = expToCExpGeneral a 

instance ExpToCExp Word where 
  expToCExp (Literal a) = cLiteral (WordVal a) CWord
  expToCExp a = expToCExpGeneral a 

instance ExpToCExp Word8 where 
  expToCExp (Literal a) = cLiteral (Word8Val a) CWord8
  expToCExp a = expToCExpGeneral a 

instance ExpToCExp Word16 where 
  expToCExp (Literal a) = cLiteral (Word16Val a) CWord16
  expToCExp a = expToCExpGeneral a 

instance ExpToCExp Word32 where 
  expToCExp (Literal a) = cLiteral (Word32Val a) CWord32
  expToCExp a = expToCExpGeneral a 

instance ExpToCExp Word64 where 
  expToCExp (Literal a) = cLiteral (Word64Val a) CWord64
  expToCExp a = expToCExpGeneral a 

  
expToCExpGeneral :: ExpToCExp a  => Exp a -> CExpr
expToCExpGeneral WarpSize      = cWarpSize 
expToCExpGeneral (BlockIdx d)  = cBlockIdx d
expToCExpGeneral (BlockDim d)  = cBlockDim d 
expToCExpGeneral (ThreadIdx d) = cThreadIdx d

expToCExpGeneral e@(Index (name,[])) = cVar name (typeToCType (typeOf e))
expToCExpGeneral e@(Index (name,xs)) = cIndex (cVar name (CPointer (typeToCType (typeOf e))),map expToCExp xs) (typeToCType (typeOf e)) 
expToCExpGeneral e@(If b e1 e2)      = cCond  (expToCExp b) (expToCExp e1) (expToCExp e2) (typeToCType (typeOf e))

expToCExpGeneral (UnOp Word32ToInt32 e) = cCast (expToCExp e) CInt32
expToCExpGeneral (UnOp Int32ToWord32 e) = cCast (expToCExp e) CWord32
expToCExpGeneral (UnOp Word32ToFloat e) = cCast (expToCExp e) CFloat
expToCExpGeneral (UnOp Word32ToWord8 e) = cCast (expToCExp e) CWord8 

expToCExpGeneral e@(BinOp Min e1 e2) = cFuncExpr "min" [expToCExp e1, expToCExp e2] (typeToCType (typeOf e)) 
expToCExpGeneral e@(BinOp Max e1 e2) = cFuncExpr "max" [expToCExp e1, expToCExp e2] (typeToCType (typeOf e)) 
expToCExpGeneral e@(BinOp op e1 e2)  = cBinOp (binOpToCBinOp op) (expToCExp e1) (expToCExp e2) (typeToCType (typeOf e)) 

expToCExpGeneral (UnOp Exp e)        = cFuncExpr "exp" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Sqrt e)       = cFuncExpr "sqrt" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Log e)        = cFuncExpr "log" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Log2 e)       = cFuncExpr "log2" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Log10 e)      = cFuncExpr "log10" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Log1p e)      = cFuncExpr "log1p" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Expm1 e)      = cFuncExpr "expm1" [expToCExp e] (typeToCType (typeOf e))

-- Floating trig
expToCExpGeneral (UnOp Sin e)        = cFuncExpr "sin" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Cos e)        = cFuncExpr "cos" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp Tan e)        = cFuncExpr "tan" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp ASin e)       = cFuncExpr "asin" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp ACos e)       = cFuncExpr "acos" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp ATan e)       = cFuncExpr "atan" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp SinH e)       = cFuncExpr "sinh" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp CosH e)       = cFuncExpr "cosh" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp TanH e)       = cFuncExpr "tanh" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp ASinH e)      = cFuncExpr "asinh" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp ACosH e)      = cFuncExpr "acosh" [expToCExp e] (typeToCType (typeOf e))
expToCExpGeneral (UnOp ATanH e)      = cFuncExpr "atanh" [expToCExp e] (typeToCType (typeOf e))
 
expToCExpGeneral e@(UnOp op e1)     = cUnOp  (unOpToCUnOp op) (expToCExp e1) (typeToCType (typeOf e))
 

typeToCType Bool = CInt 
typeToCType Int  = CInt
typeToCType Int8  = CInt8
typeToCType Int16  = CInt16
typeToCType Int32  = CInt32
typeToCType Int64  = CInt64
typeToCType Float = CFloat
typeToCType Double = CDouble
typeToCType Word8 = CWord8
typeToCType Word16 = CWord16
typeToCType Word32 = CWord32
typeToCType Word64 = CWord64
typeToCType (Pointer t) = CPointer (typeToCType t)
typeToCType (Global t)  = CQualified CQualifyerGlobal (typeToCType t) 
typeToCType (Local t)  = CQualified CQualifyerLocal (typeToCType t) 

-- maybe unnecessary
binOpToCBinOp Add = CAdd
binOpToCBinOp Sub = CSub
binOpToCBinOp Mul = CMul
binOpToCBinOp Div = CDiv 
binOpToCBinOp FDiv = CDiv -- (???)  
binOpToCBinOp Mod = CMod

binOpToCBinOp Eq  = CEq 
binOpToCBinOp NotEq = CNotEq
binOpToCBinOp Lt  = CLt 
binOpToCBinOp LEq = CLEq
binOpToCBinOp Gt  = CGt 
binOpToCBinOp GEq = CGEq 

binOpToCBinOp And = CAnd 
binOpToCBinOp Or  = COr 

binOpToCBinOp Pow = CPow

binOpToCBinOp BitwiseAnd = CBitwiseAnd
binOpToCBinOp BitwiseOr  = CBitwiseOr
binOpToCBinOp BitwiseXor = CBitwiseXor
binOpToCBinOp ShiftL     = CShiftL 
binOpToCBinOp ShiftR     = CShiftR
-- notice min and max is not here ! 

unOpToCUnOp   BitwiseNeg = CBitwiseNeg
unOpToCUnOp   Not = CNot

