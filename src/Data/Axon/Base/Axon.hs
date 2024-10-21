module Data.Axon.Base.Axon where

import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM.TArray
import Control.Core.Composition
import Control.Base.Comonad

-- Array

type AdjArrayL i a = Env (TArray i a)

type AdjArrayR i a = Reader (TArray i a)

adjDrowLineV ::
  ( Monad m
  , Ix x, Ix y
  , MonadIO m
  ) =>
  (x,y) ->
  (x,y) ->
  a ->
  M.AdjointT 
    (AdjArrayL (x,y) a)
    (AdjArrayR (x,y) a)
    m
    ()
adjDrowLineV (x0',y0') (x1',y1') a = do
  let (x0,x1) = if y0' > y1' then (x1',x0') else (x0',x1')
  let (y0,y1) = if y0' > y1' then (y1',y0') else (y0',y1')

  let dx' = x1 - x0
  let dy' = y1 - y0

  let dir = if dy' < 0 then (-1) else 1
  let dy = dir * dy

  if dx' /= 0 then do
    f2 y0 (2*dy - dx')
    {-let x = x0
    p
  -}
  where
    f y p i | i <= (dx' + 1) = do 
      (y2,p2) <- f2 y p
      f y2 p2 (i + 1)
    f2 y p =
      -- forM (range 0 (dx' + 1)) (\i->do
      arr <- adjGetEnv
      arr' <- liftIO $ writeArray (x0+i,y) a
      adjSetEnv arr' (pure ())
      if p >= 0
        then return (y + dir, p - 2 * dx')
        else return (y, p + 2*dy)
      --  )
