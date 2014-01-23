import qualified Prelude
import Feldspar
import Feld.ObsComp

func :: Data Int32 -> Data Int32 -> Data Int32 -> Data Bool
func a b c = a + b == c

tf0 = eval (func 3 4 5)
tf1 = icompile func
tf2 = icompile (func 3)



