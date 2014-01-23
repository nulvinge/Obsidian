{-# LANGUAGE FlexibleInstances,
             OverlappingInstances,
             UndecidableInstances,
             FlexibleContexts,
             MultiParamTypeClasses,
             TypeOperators,
             TypeFamilies ,
             ScopedTypeVariables,
             GADTs,
             ConstraintKinds
             #-}

module Feld.ObsComp where

import Data.Char
import System.FilePath
import Data.Typeable as DT
import Control.Arrow
import Control.Applicative

import Control.Monad.RWS

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder

import Feldspar.Core.Types
import Feldspar.Core.Interpretation
import Feldspar.Core.Constructs
import Feldspar.Core.Constructs.Binding
import Feldspar.Core.Frontend

import Feldspar.Compiler.Imperative.Representation (Module)
import Feldspar.Compiler.Imperative.Frontend hiding (Type)
import Feldspar.Compiler.Imperative.FromCore.Interpretation
import Feldspar.Compiler.Imperative.FromCore.Array ()
import Feldspar.Compiler.Imperative.FromCore.Binding ()
import Feldspar.Compiler.Imperative.FromCore.Condition ()
import Feldspar.Compiler.Imperative.FromCore.ConditionM ()
import Feldspar.Compiler.Imperative.FromCore.Error ()
import Feldspar.Compiler.Imperative.FromCore.FFI ()
import Feldspar.Compiler.Imperative.FromCore.Future ()
import Feldspar.Compiler.Imperative.FromCore.Literal ()
import Feldspar.Compiler.Imperative.FromCore.Loop ()
import Feldspar.Compiler.Imperative.FromCore.Mutable ()
import Feldspar.Compiler.Imperative.FromCore.MutableToPure ()
import Feldspar.Compiler.Imperative.FromCore.NoInline ()
import Feldspar.Compiler.Imperative.FromCore.Par ()
import Feldspar.Compiler.Imperative.FromCore.Primitive ()
import Feldspar.Compiler.Imperative.FromCore.Save ()
import Feldspar.Compiler.Imperative.FromCore.SizeProp ()
import Feldspar.Compiler.Imperative.FromCore.SourceInfo ()
import Feldspar.Compiler.Imperative.FromCore.Tuple ()

import qualified Obsidian.Program as P
import qualified Obsidian.CodeGen.Program as CG
import qualified Obsidian as O

import Data.List

icompile :: (SyntacticFeld a) => a -> IO ()
icompile prg = icompile' prg "test"

icompile' prg functionName = do
    putStrLn "=============== Source ================"
    -- putStrLn $ src
    putStrLn "=============== Source ================"
    -- putStrLn $ unlines $ intersperse "" $ map (show.procBody) $ entities m
    putStrLn "=============== Source ================"
    -- O.printAnalysis m ()
  where
    -- m = fromCore functionName prg
    -- m = executePluginChain' Interactive prg fsignature opts
    -- fsignature = NameExtractor.OriginalFunctionSignature functionName []
    -- (dbgModule, (src, endPos)) = compToCWithInfos ((opts,Declaration_pl), 1) m

    astf = reifyFeld N32 prg
    

compileProgTop :: (Compile dom dom, Project (CLambda Type) dom) =>
    String -> [Var] -> ASTF (Decor Info dom) a -> Mod
compileProgTop funname args (lam :$ body)
    | Just (SubConstr2 (Lambda v)) <- prjLambda lam
    = let ta  = argType $ infoType $ getInfo lam
          sa  = defaultSize ta
          var = mkVariable (compileTypeRep ta sa) v
       in compileProgTop funname (var:args) body
compileProgTop funname args a = Mod defs
  where
    ins      = reverse args
    info     = getInfo a
    outType  = compileTypeRep (infoType info) (infoSize info)
    outParam = Pointer outType "out"
    outLoc   = Ptr outType "out"
    results  = snd $ evalRWS (compileProg outLoc a) initReader initState
    Bl ds p  = block results
    defs     = def results ++ [ProcDf funname ins [outParam] (Block ds p)]



