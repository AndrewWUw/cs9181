import System.IO.Unsafe
import System.Environment

import Data.Char  
import Data.Int
import Prelude

import Data.Array.Accelerate                    as A hiding ( size )
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.C
--import Data.Array.Accelerate.C.Exp

type F            = Float       -- Double not supported on all devices

type Complex      = (F,F)
type ComplexPlane = Array DIM2 Complex

next :: Exp Complex -> Exp Complex -> Exp Complex
next c z = c `plus` (z `times` z)


plus :: Exp Complex -> Exp Complex -> Exp Complex
plus = lift2 f
  where f :: (Exp F, Exp F) -> (Exp F, Exp F) -> (Exp F, Exp F)
        f (x1,y1) (x2,y2) = (x1+x2,y1+y2)

times :: Exp Complex -> Exp Complex -> Exp Complex
times = lift2 f
  where f :: (Exp F, Exp F) -> (Exp F, Exp F) -> (Exp F, Exp F)
        f (ax,ay) (bx,by)   =  (ax*bx-ay*by, ax*by+ay*bx)

dot :: Exp Complex -> Exp F
dot = lift1 f
  where f :: (Exp F, Exp F) -> Exp F
        f (x,y) = x*x + y*y

--main :: IO ()
--main = do
--    let x = constant 3
--    putStrLn "hi"
