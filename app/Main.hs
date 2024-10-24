
import Data.Axon.Base.Axon
import Control.Monad.STM
import Graphics.Gloss.Data.Color
import Graphics.Gloss.Data.Picture
import Graphics.Gloss.Interface.Pure.Display
import Data.Array.MArray
import Control.Base.Comonad
import Data.Functor.Identity

main = do
  arr <- newArray ((0,0),(100,100)) (Color black cube)
  let w = adjEnv arr (Identity ()) 
  pic <- atomically $ do
    adjCoDrowLine (1,1) (100,100) (fmap (const $ Color white cube) w)
    adjCoDrowLine (50,25) (0,0) (fmap (const $ Color white cube) w)
    adjCoDrowArray id w
  display 
    (InWindow "test" (100,100) (0,0))
    black
    pic
