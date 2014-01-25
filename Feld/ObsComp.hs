{-# LANGUAGE FlexibleInstances,
             OverlappingInstances,
             UndecidableInstances,
             FlexibleContexts,
             MultiParamTypeClasses,
             TypeOperators,
             TypeFamilies ,
             ScopedTypeVariables,
             GADTs,
             RankNTypes
             #-}

module Feld.ObsComp where

import Feldspar.Compiler.Imperative.FromCore
import Feldspar.Compiler.Backend.C.Options
import qualified Feldspar.NameExtractor as NameExtractor
import Feldspar.Compiler.Backend.C.Library
import Feldspar.Compiler.Imperative.Representation
import Feldspar.Compiler.Backend.C.Plugin.PrettyPrint
import Feldspar.Compiler.Backend.C.Plugin.Locator

import Data.Char
import System.FilePath
import Data.Typeable as DT
import Control.Arrow
import Control.Applicative

import Feldspar.Transformation
import qualified Feldspar.NameExtractor as NameExtractor
import Feldspar.Compiler.Backend.C.Library
import Feldspar.Compiler.Backend.C.Options
import Feldspar.Compiler.Backend.C.Platforms
import Feldspar.Compiler.Backend.C.Plugin.Rule
import Feldspar.Compiler.Backend.C.Plugin.TypeDefinitionGenerator
import Feldspar.Compiler.Backend.C.Plugin.VariableRoleAssigner
import Feldspar.Compiler.Backend.C.Plugin.BlockProgramHandler
import Feldspar.Compiler.Backend.C.Plugin.TypeCorrector
import Feldspar.Compiler.Backend.C.Plugin.PrettyPrint
import Feldspar.Compiler.Imperative.FromCore
import Feldspar.Compiler.Imperative.Plugin.ConstantFolding
import Feldspar.Compiler.Imperative.Plugin.Free
import Feldspar.Compiler.Imperative.Plugin.IVars
import Feldspar.Compiler.Imperative.Plugin.Naming
import Feldspar.Compiler.Imperative.Plugin.Unroll

import qualified Obsidian.Program as P
import qualified Obsidian.CodeGen.Program as CG
import qualified Obsidian as O

import Feldspar.Core.Types hiding (Type, BoolType, FloatType, ArrayType)
import Feldspar.Core.Frontend

import Data.List

icompile :: (Compilable t internal) => t -> IO ()
icompile prg = icompile' prg "test" defaultOptions

icompile' :: (Compilable t internal) => t -> String -> Options -> IO ()
icompile' prg functionName opts = do
    putStrLn "=============== Source ================"
    putStrLn $ src
    putStrLn "=============== Source ================"
    putStrLn $ show $ astf
    putStrLn "=============== Source ================"
    putStrLn $ unlines $ intersperse "" $ map (show.procBody) $ entities m
    putStrLn "=============== Source ================"
    O.printAnalysis m ()
  where
    -- m = fromCore functionName prg
    m = executePluginChain' Interactive prg fsignature opts
    fsignature = NameExtractor.OriginalFunctionSignature functionName []
    (dbgModule, (src, endPos)) = compToCWithInfos ((opts,Declaration_pl), 1) m
    astf = reifyFeld N32 prg

convType :: Variable t -> (O.Name,O.Type)
convType v = (varName v, convT $ varType v)
convT :: Type -> O.Type
convT BoolType = O.Bool
convT FloatType = O.Float
convT (NumType Signed S8)  = O.Int8
convT (NumType Signed S16) = O.Int16
convT (NumType Signed S32) = O.Int32
convT (NumType Signed S64) = O.Int64
convT (NumType Unsigned S8)  = O.Word8
convT (NumType Unsigned S16) = O.Word16
convT (NumType Unsigned S32) = O.Word32
convT (NumType Unsigned S64) = O.Word64
convT (ArrayType s t) = O.Pointer (convT t)

makeIM :: Block () -> [Variable t] -> CG.IM
makeIM b o = map ((\(n,t) -> (CG.SOutput n 0 t,())) . convType) o
          ++ makeBlock b

makeBlock :: Block () -> CG.IM
makeBlock (Block l b ll) = makeProg b

makeProg :: Program () -> CG.IM
makeProg (Empty _ _) = []
makeProg (Comment _ s _ _) = [(CG.SComment s, ())]
makeProg (Assign  l r _ _) = case makeExpr r of Ebox e -> [(CG.SAssign name inds e, ())]
  where (name, inds) = makeLHS l
makeProg (Sequence p _ _) = concatMap makeProg p
makeProg (Branch   c t f _ _) = [(CG.SCond cc          (makeBlock t), ())
                                ,(CG.SCond (O.notE cc) (makeBlock t), ())
                                ]
  where cc = makeExp O.BoolWitness c
makeProg (SeqLoop c condCalc b _ _) = [(CG.SFor O.Seq O.Unknown "test" (makeExp O.Word32Witness c)
                                                (makeBlock b ++ makeBlock condCalc), ())]
makeProg (ParLoop v c 1 b _ _) = [(CG.SFor O.Par O.Unknown name 65536 -- (makeExp O.Word32Witness c)
                                           (makeBlock b), ())]
  where (name,t) = convType v
makeProg (BlockProgram b _) = makeBlock b
makeProg (ProcedureCall n p _ _) = makeCall n p
makeProg a = error $ "Prog: " ++ show a

makeCall "initArray" [Out (VarExpr v _) _, In (SizeOf t _ _) _, In e _] = [] -- [(CG.SOutput n e' t', ())]
  where e' = makeExp O.Word32Witness e
        (n,t')  = convType v

makeExpr :: Expression () -> EBox
makeExpr (VarExpr v _) = makeEBox t (\_ -> O.Index (n,[]))
  where (n,t) = convType v
makeExpr (ArrayElem (VarExpr v _) i _ _) = makeEBox t (\_ -> O.Index (n,[makeExp O.Word32Witness i]))
  where (n,t) = convType v
makeExpr (ConstExpr (IntConst v t _ _) _) = makeEBoxN t' (\_ -> (O.Literal $ fromIntegral v))
  where t' = convT t
makeExpr (ConstExpr (FloatConst v _ _) _) = Ebox $ O.Literal $ v
makeExpr (ConstExpr (BoolConst  v _ _) _) = Ebox $ O.Literal $ v
makeExpr (FunctionCall f p _ _) = Ebox $ makeFun O.Word32Witness (funName f) p
  where t = convT $ returnType f

makeEBox :: O.Type -> (forall a. (O.Scalar a) => () -> O.Exp a) -> EBox
makeEBox O.Bool f = Ebox (f () :: O.EBool)

makeEBoxN :: O.Type -> (forall a. (O.Scalar a, Num a) => () -> O.Exp a) -> EBox
makeEBoxN O.Word32 f = Ebox (f () :: O.EWord32)

makeExp :: (O.Scalar t) => O.Witness t -> Expression () -> O.Exp t
makeExp _ (VarExpr v _) = O.Index (n,[])
  where (n,t) = convType v
makeExp _ (ArrayElem (VarExpr v _) i _ _) = O.Index (n,[makeExp O.Word32Witness i])
  where (n,t) = convType v
makeExp O.Word32Witness (ConstExpr (IntConst v t _ _) _) = O.Literal $ fromIntegral v
-- makeExp O.DoubleWitness (ConstExpr (FloatConst v _ _) _) = O.Literal $ v
makeExp O.BoolWitness (ConstExpr (BoolConst  v _ _) _) = O.Literal $ v
makeExp w (FunctionCall f p _ _) = makeFun w (funName f) p

makeFun :: (O.Scalar t) => O.Witness t -> String -> [Expression ()] -> O.Exp t
makeFun O.BoolWitness "==" [a,b] = (O.==*) (makeExp O.Word32Witness a) (makeExp O.Word32Witness b)
makeFun O.Word32Witness "+" [a,b] = (+) (makeExp O.Word32Witness a) (makeExp O.Word32Witness b)
makeFun O.Word32Witness "*" [a,b] = (*) (makeExp O.Word32Witness a) (makeExp O.Word32Witness b)
makeFun O.Word32Witness "min" [a,b] = O.minE (makeExp O.Word32Witness a) (makeExp O.Word32Witness b)
makeFun O.Word32Witness "getLength" [a] = 65536
makeFun w f a = error $ show $ (f,a)

data EBox where
  Ebox :: (O.Scalar a) => O.Exp a -> EBox

{-
expWitness :: Expression () -> (forall a. (O.Scalar a) => () -> O.Witness a)
expWitness = t2w . convT . exprT
  where
    exprT (VarExpr v _) = varType v
    exprT (ArrayElem (VarExpr v _) _ _ _) = t
      where ArrayType l t = varType v
    exprT (ConstExpr (IntConst v t _ _) _) = t
    exprT (ConstExpr (FloatConst v _ _) _) = FloatType
    exprT (ConstExpr (BoolConst  v _ _) _) = BoolType
    exprT (FunctionCall f p _ _) = returnType f

    t2w :: O.Type -> (forall a. (O.Scalar a) => () -> O.Witness a)
    t2w O.Word32 = \() -> O.Word32Witness
    t2w O.Bool   = \() -> O.BoolWitness
-}

makeLHS (VarExpr v _) = case varRole v of
  Value   -> (varName v, [])
  Pointer -> (varName v, [0])
makeLHS (ArrayElem (VarExpr v _) i _ _) = (varName v, [makeExp O.Word32Witness i])
makeLHS a = error $ "LHS: " ++ show a



instance O.ToProgram (Module ()) where
  toProgram 0 m () = O.traces ins (ins,sizes,im)
    where
      ProcDef n i o b _ _ = head $ entities $ m
      ins = map convType i
      sizes = []
      im = makeIM b o

type instance O.InputList (Module ()) = () 

defaultOptions :: Options
defaultOptions
    = Options
    { platform          = c99
    , unroll            = NoUnroll
    , debug             = NoDebug
    , memoryInfoVisible = True
    , rules             = []
    }

pluginChain :: ExternalInfoCollection -> Module () -> Module ()
pluginChain externalInfo
    = executePlugin RulePlugin (ruleExternalInfo externalInfo)
    . executePlugin TypeDefinitionGenerator (typeDefinitionGeneratorExternalInfo externalInfo)
    . executePlugin ConstantFolding ()
    . executePlugin UnrollPlugin (unrollExternalInfo externalInfo)
    . executePlugin Precompilation (precompilationExternalInfo externalInfo)
    . executePlugin RulePlugin (primitivesExternalInfo externalInfo)
    . executePlugin Free ()
    . executePlugin IVarPlugin ()
    . executePlugin VariableRoleAssigner (variableRoleAssignerExternalInfo externalInfo)
    . executePlugin TypeCorrector (typeCorrectorExternalInfo externalInfo)
    . executePlugin BlockProgramHandler ()

data ExternalInfoCollection = ExternalInfoCollection {
      precompilationExternalInfo          :: ExternalInfo Precompilation
    , unrollExternalInfo                  :: ExternalInfo UnrollPlugin
    , primitivesExternalInfo              :: ExternalInfo RulePlugin
    , ruleExternalInfo                    :: ExternalInfo RulePlugin
    , typeDefinitionGeneratorExternalInfo :: ExternalInfo TypeDefinitionGenerator
    , variableRoleAssignerExternalInfo    :: ExternalInfo VariableRoleAssigner
    , typeCorrectorExternalInfo           :: ExternalInfo TypeCorrector
}

executePluginChain' :: (Compilable c internal)
  => CompilationMode -> c -> NameExtractor.OriginalFunctionSignature
  -> Options -> Module ()
executePluginChain' compMode prg originalFunctionSignatureParam opt =
  pluginChain ExternalInfoCollection {
    precompilationExternalInfo = PrecompilationExternalInfo {
        originalFunctionSignature = fixedOriginalFunctionSignature
      , inputParametersDescriptor = buildInParamDescriptor prg
      , numberOfFunctionArguments = numArgs prg
      , compilationMode           = compMode
      }
    , unrollExternalInfo                  = unroll opt
    , primitivesExternalInfo              = opt{ rules = platformRules $ platform opt }
    , ruleExternalInfo                    = opt
    , typeDefinitionGeneratorExternalInfo = opt
    , variableRoleAssignerExternalInfo    = ()
    , typeCorrectorExternalInfo           = False
    } $ fromCore "PLACEHOLDER" prg
  where
    ofn = NameExtractor.originalFunctionName
    fixedOriginalFunctionSignature = originalFunctionSignatureParam {
      NameExtractor.originalFunctionName =
        fixFunctionName $ ofn originalFunctionSignatureParam
    }

