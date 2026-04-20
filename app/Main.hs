
import Data.Axon.Base.Axon
import Control.Monad.STM
import Graphics.Gloss.Data.Color
import Graphics.Gloss.Data.Picture
import Graphics.Gloss.Interface.Pure.Display
import Data.Array.MArray
import Control.Base.Comonad
import Data.Functor.Identity
import Data.Map as Map
import Data.Set as Set

import Visual

main = mainPingPong

initialDisplay pic = display
  (InWindow "test" (1000,1000) (0,0))
  black 
  pic 

initialComonad arr = adjEnv arr (Identity ())

initialArray = newArray ((0,0),(1000,1000)) (Color black cube)

mainRedBox = do
  arr <- initialArray
  let w = initialComonad arr
  _ <- updateIn2BoxRedPic 40 110 (500,500) w
  pic <- drowWPic w
  initialDisplay pic 


