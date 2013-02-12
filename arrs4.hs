{-# LANGUAGE MultiParamTypeClasses,  
             FlexibleInstances,
             FlexibleContexts,
             UndecidableInstances,
             ScopedTypeVariables,
             GADTs, 
             TypeFamilies #-}


import Obsidian.Exp
import Obsidian.Types
import Obsidian.Globs
import Obsidian.Program
--import Obsidian.Array
--import Obsidian.Force

import Data.List
import Data.Word

data Pull s a = Pull s (s -> a)

data Push s a = Push s ((a -> s -> Program Thread ()) -> Program Grid ())



