import qualified Prelude
import Feldspar
import Feldspar.Vector
import Feld.ObsComp
-- import Feldspar.Compiler.Frontend.Interactive.Interface

func :: Data Word32 -> Data Word32 -> Data Word32 -> Data Word32
func a b c = a + b * c

tf0 = eval (func 3 4 5)
tf1 = icompile func
tf2 = icompile (func 3)


scProd :: (Syntax a, Num a) => Vector a -> Vector a -> a
scProd a b = sum (zipWith (*) a b)

saxpy :: (Syntax a, Num a) => Vector a -> Vector a -> Vector a
saxpy a b = zipWith (*) a b

saxpyF = saxpy :: Vector (Data Word32) -> Vector (Data Word32) -> Vector (Data Word32)
ts0 = icompile saxpyF


