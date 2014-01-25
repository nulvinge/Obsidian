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
{-
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
-}
--import Feld.Interpretation

import Feldspar.Core.Types as Core
import qualified Feldspar.Core.Constructs.Binding as Core
import Feldspar.Core.Constructs.Condition
import Feldspar.Core.Types (Type)
import Feldspar.Core.Constructs.Bits
import Feldspar.Core.Constructs.Complex
import Feldspar.Core.Constructs.Conversion
import Feldspar.Core.Constructs.Eq
import Feldspar.Core.Constructs.Floating
import Feldspar.Core.Constructs.Fractional
import Feldspar.Core.Constructs.Integral
import Feldspar.Core.Constructs.Logic
import Feldspar.Core.Constructs.Num
import Feldspar.Core.Constructs.Ord
import Feldspar.Core.Constructs.Trace
import Feldspar.Core.Constructs.Literal
import Feldspar.Core.Constructs.Loop hiding (For, While)
import Feldspar.Core.Constructs.Literal
import qualified Feldspar.Core.Constructs.Loop as Core
import Feldspar.Core.Constructs.Tuple
import Feldspar.Core.Constructs.Error
import Feldspar.Core.Constructs.Future
import Feldspar.Core.Constructs.FFI
import Feldspar.Core.Constructs.Array
import Feldspar.Core.Constructs.NoInline
import Feldspar.Core.Constructs.Save
import Feldspar.Core.Constructs.ConditionM
import Feldspar.Core.Constructs.Binding
import Feldspar.Core.Constructs.Mutable
import Feldspar.Core.Constructs.MutableArray
import Feldspar.Core.Constructs.MutableReference
import Feldspar.Core.Constructs.MutableToPure
import Feldspar.Core.Constructs.SizeProp
import Feldspar.Core.Constructs.Par

import Feldspar.Compiler.Imperative.Frontend hiding (Type)

import qualified Obsidian.Program as P
import qualified Obsidian.CodeGen.Program as CG
import qualified Obsidian as O
import Feldspar.Core.Constructs.SourceInfo

import Data.List

icompile :: (SyntacticFeld a) => a -> IO ()
icompile prg = icompile' prg "test"

icompile' :: (SyntacticFeld a) => a -> String -> IO ()
icompile' prg functionName = do
    putStrLn "=============== Source ================"
    putStrLn $ show $ astf
    putStrLn "=============== Source ================"
    putStrLn $ show $ p
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
    p = compileProgTop functionName []
      $ reifyFeld N32 prg

compileProgTop :: (Compile dom dom, Project (CLambda Type) dom) =>
    String -> O.Inputs -> ASTF (Decor Info dom) a -> CG.IM
compileProgTop funname args (lam :$ body)
    | Just (SubConstr2 (Lambda v)) <- prjLambda lam
    = let ta  = argType $ infoType $ getInfo lam
          sa  = defaultSize ta
          name = ("input" ++ (show $ length args))
          -- var = O.variable name
       in compileProgTop funname ((name,convType ta):args) body
compileProgTop funname args a =
  [(CG.SOutput "out" outSize outType, ())]
  ++ compileProg' "out" a
  where
    ins      = reverse args
    info     = getInfo a
    outType  = O.Pointer $ convType $ infoType info
    outSize :: O.EWord32
    outSize  = 1 -- infoSize info

convType :: Feldspar.Core.Types.TypeRep a -> O.Type
convType = undefined

data EBox where
  Ebox :: (O.Scalar a) => O.Exp a -> EBox

class Compile sub dom where
  compileProg :: sub a -> O.Name -> Args (AST (Decor Info dom)) a -> CG.IM
  compileProg a n args = case compileExpr a args of
    Ebox e -> [(CG.SAssign n [] e,())]
  compileExpr :: sub a -> Args (AST (Decor Info dom)) a -> EBox
  compileExpr a args = error "p2e"
                    -- [(SDeclare "e", ())]
                    -- ++ compileProg "e" a args

instance Compile FeldDomain FeldDomain where
  compileProg (C' a) = compileProg a

instance Compile Empty FeldDomain where
  compileProg _ = error "Can't compile Empty"

instance Compile (AST (Decor Info dom)) dom where
  compileProg = undefined

instance Compile (CLambda Type) dom where
  compileProg = error "Can only compile top level lambda"

instance Compile (Core.Variable :|| Type) dom where
  compileExpr (C' (Core.Variable v)) Nil = Ebox ((O.variable $ show v) ::
    where 
      -- boxType :: Feldspar.Compiler.Imperative.Frontend.Type -> VarId -> EBox
      boxType Boolean v = Ebox ((O.variable $ show v) :: O.EBool)

instance (Compile sub1 dom, Compile sub2 dom) => Compile (sub1 :+: sub2) dom where
  compileProg (InjL a) = compileProg a
  compileProg (InjR a) = compileProg a


compileProgDecor :: Compile dom dom
    => O.Name
    -> Decor Info dom a
    -> Args (AST (Decor Info dom)) a
    -> CG.IM
compileProgDecor l (Decor info a) args =
    let src = infoSource info
    -- unless (null src) $ tellProg [BComment src]
    in compileProg a l args

compileProg' l a = simpleMatch (compileProgDecor l) a

instance Compile dom dom => Compile (Condition :|| Core.Type) dom where
  compileProg (C' Condition) l (cond :* tHEN :* eLSE :* Nil) =
    undefined

  {- do
    condExpr <- compileExpr cond
    (_, Bl tds thenProg) <- confiscateBlock $ compileProg loc tHEN
    (_, Bl eds elseProg) <- confiscateBlock $ compileProg loc eLSE
    tellProg [If condExpr (Block tds thenProg) (Block eds elseProg)]
  -}

instance Compile (Literal :|| Core.Type) dom
  where
    compileProg = undefined
    --compileExprSym (C' (Literal a)) info Nil = literal (infoType info) (infoSize info) a

instance ( Compile dom dom
         , Project (CLambda Type) dom
         , Project (Literal  :|| Type) dom
         , Project (Variable :|| Type) dom
         )
      => Compile (Loop :|| Type) dom
  where
    compileProg (C' ForLoop) l (len :* init :* (lam1 :$ (lam2 :$ ixf)) :* Nil)
        | Just (SubConstr2 (Lambda ix)) <- prjLambda lam1
        , Just (SubConstr2 (Lambda st)) <- prjLambda lam2
        = let info1 = getInfo lam1
              info2 = getInfo lam2
              -- (Var _ name) = mkVar (compileTypeRep (infoType info1) (infoSize info1)) ix
              -- stvar        = mkVar (compileTypeRep (infoType info2) (infoSize info2)) st
          in undefined

{-
            len' <- mkLength len
            compileProg loc init
            (_, Bl ds body) <- withAlias st loc $ confiscateBlock $ compileProg stvar ixf >> assign loc stvar
            declare stvar
            tellProg [For name len' 1 (Block ds body)]
-}

instance ( Compile dom dom
         , Project (CLambda Type) dom
         , Project (Literal  :|| Type) dom
         , Project (Variable :|| Type) dom
         )
      => Compile (LoopM Mut) dom
  where
    compileProg Core.For l (len :* (lam :$ ixf) :* Nil)
        | Just (SubConstr2 (Lambda v)) <- prjLambda lam
        = let ta = argType $ infoType $ getInfo lam
              sa = defaultSize ta
              -- (Var _ name) = mkVar (compileTypeRep ta sa) v
          in undefined
          {-
            len' <- mkLength len
            (_, Bl _ body) <- confiscateBlock $ compileProg loc ixf
            tellProg [For name len' 1 body]
          -}

-- | Converts symbols to primitive function calls
instance Compile dom dom => Compile Semantics dom
  where
    compileProg = undefined
{-
    compileExprSym (Sem name _) info args = do
        argExprs <- sequence $ listArgs compileExpr args
        return $ Fun (compileTypeRep (infoType info) (infoSize info)) name argExprs
-}

instance Compile dom dom => Compile (BITS       :|| Type) dom where compileExpr = error "1"
instance Compile dom dom => Compile (COMPLEX    :|| Type) dom where compileExpr = error "2"
instance Compile dom dom => Compile (Conversion :|| Type) dom where compileExpr = error "3"
instance Compile dom dom => Compile (EQ         :|| Type) dom where compileExpr = error "4"
instance Compile dom dom => Compile (FLOATING   :|| Type) dom where compileExpr = error "5"
instance Compile dom dom => Compile (FRACTIONAL :|| Type) dom where compileExpr = error "6"
instance Compile dom dom => Compile (INTEGRAL   :|| Type) dom where compileExpr = error "7"
instance Compile dom dom => Compile (Logic      :|| Type) dom where compileExpr = error "8"
instance Compile dom dom => Compile (NUM        :|| Type) dom where compileExpr = error "9"
instance Compile dom dom => Compile (ORD        :|| Type) dom where compileExpr = error "10"
instance Compile dom dom => Compile (Trace      :|| Type) dom where compileExpr = error "11"

instance Compile dom dom => Compile ((Decor SourceInfo1 Identity) :|| Type) dom
  where
    compileProg (C' (Decor (SourceInfo1 info) Id)) l (a :* Nil) =
        compileProg' l a

instance Compile dom dom => Compile (Tuple :|| Type) dom
  where
    compileProg (C' Tup2) l (m1 :* m2 :* Nil) = undefined
    {-
        compileExpr m1 >>= assign (loc :.: "member1")
        compileExpr m2 >>= assign (loc :.: "member2")
    -}

instance Compile dom dom => Compile (Select :|| Type) dom
  where
    compileProg = undefined
    {-
        compileExprSym (C' Sel1) _ (tup :* Nil) = undefined
        tupExpr <- compileExpr tup
        return $ tupExpr :.: "member1"
    -}

{-
type FeldSymbols
=   (Decor SourceInfo1 Identity :|| Type)
:+: (Condition  :|| Type)
    :+: (FFI        :|| Type)
    :+: (Let        :|| Type)
:+: (Literal    :|| Type)
:+: (Select     :|| Type)
:+: (Tuple      :|| Type)
    :+: (Array      :|| Type)
:+: (BITS       :|| Type)
:+: (COMPLEX    :|| Type)
:+: (Conversion :|| Type)
:+: (EQ         :|| Type)
    :+: (Error      :|| Type)
:+: (FLOATING   :|| Type)
:+: (FRACTIONAL :|| Type)
    :+: (FUTURE     :|| Type)
:+: (INTEGRAL   :|| Type)
:+: (Logic      :|| Type)
:+: (Loop       :|| Type)
:+: (NUM        :|| Type)
    :+: (NoInline   :|| Type)
:+: (ORD        :|| Type)
    :+: (PropSize   :|| Type)
    :+: (Save       :|| Type)
:+: (Trace      :|| Type)
    :+: ConditionM Mut
:+: LoopM Mut
    :+: MONAD Mut
    :+: Mutable
    :+: MutableArray
    :+: MutableReference
    :+: MutableToPure
    :+: MONAD Par
    :+: ParFeature
    :+: Empty

-}

instance Compile dom dom => Compile (FFI        :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (Let        :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (Array      :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (Error      :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (FUTURE     :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (NoInline   :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (PropSize   :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (Save       :|| Type) dom where compileProg = undefined
instance Compile dom dom => Compile (ConditionM Mut     ) dom where compileProg = undefined
instance Compile dom dom => Compile (MONAD Mut          ) dom where compileProg = undefined
instance Compile dom dom => Compile (Mutable            ) dom where compileProg = undefined
instance Compile dom dom => Compile (MutableArray       ) dom where compileProg = undefined
instance Compile dom dom => Compile (MutableReference   ) dom where compileProg = undefined
instance Compile dom dom => Compile (MutableToPure      ) dom where compileProg = undefined
instance Compile dom dom => Compile (MONAD Par          ) dom where compileProg = undefined
instance Compile dom dom => Compile (ParFeature         ) dom where compileProg = undefined

