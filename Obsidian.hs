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

quickPrint :: ToProgram prg => prg -> InputList prg -> IO ()
quickPrint prg input =
  putStrLn $ genKernel "kernel" prg input 

printAnalysis :: ToProgram prg => prg -> InputList prg -> IO ()
printAnalysis = quickPrint

