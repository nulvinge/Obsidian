module Obsidian (module Obsidian.Array
                ,module Obsidian.Program
                ,module Obsidian.Globs ,module Obsidian.Exp
                ,module Obsidian.Types
                ,module Obsidian.Force
                ,module Obsidian.Library
                ,module Obsidian.LibraryG
                ,module Obsidian.CodeGen.InOut
                ,module Obsidian.CodeGen.CUDA
                ,module Obsidian.Atomic
                ,module Obsidian.SeqLoop
                ,module Obsidian.Memory
                ,module Data.Word
                ,quickPrint
                ,printAnalysis
                ,printWithStrategy
                ) where



import Obsidian.Program
import Obsidian.Globs
import Obsidian.Exp
import Obsidian.Types
import Obsidian.Array
import Obsidian.Library
import Obsidian.LibraryG
import Obsidian.Force
import Obsidian.CodeGen.InOut
import Obsidian.CodeGen.CUDA 
import Obsidian.Atomic
import Obsidian.SeqLoop
import Obsidian.Memory
import Data.Word

defaultStrategy, defaultStrategy' :: Strategy
defaultStrategy' =
  [(Par,Block,1)
  ,(Par,Thread,32)
  ,(Par,Block,32)
  ,(Par,Thread,32)
  ,(Par,Vector,4)
  ,(Par,Block,32)
  ,(Par,Block,32)
  ,(Seq,Thread,0)
  ]
defaultStrategy =
  [(Par,Block,65536)
  ,(Par,Thread,1024)
  ,(Par,Vector,4)
  ,(Par,Block,0)
  ]

quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ genKernel "kernel" defaultStrategy' prg input 

printAnalysis :: ToProgram prg => prg -> InputList prg -> IO ()
printAnalysis = quickPrint

printWithStrategy strat prg input =
  putStrLn $ genKernel "kernel" strat prg input 

