{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Axon.Base.Axon where

import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM.TArray
import Control.Core.Composition
import Control.Base.Comonad
import Graphics.Gloss.Data.Picture
import Data.Ix
import Data.Functor.Adjunction
import Control.Comonad
import Control.Comonad.Env
import Control.Monad.Reader
import Control.Comonad.Trans.Adjoint as W
import Data.Array.MArray
import Debug.Trace

-- Array

type AdjArrayL i a = Env (TArray i a)

type AdjArrayR i a = Reader (TArray i a)

adjCoDrowLineV :: 
  ( Comonad w  
  , Ix x
  , Real x
  , Show x
  ) =>
  (x,x) ->
  (x,x) ->
  W.AdjointT
    (AdjArrayL (x,x) a)
    (AdjArrayR (x,x) a)
    w
    (a -> a) ->
  STM ()
adjCoDrowLineV (x0',y0') (x1',y1') wa = let
  (x0,x1) = if y0' > y1' then (x1',x0') else (x0',x1')
  (y0,y1) = if y0' > y1' then (y1',y0') else (y0',y1')
  dx' = x1 - x0
  dy' = y1 - y0
  dir = if dy' <0 then (-1) else 1
  dx = dir * dx'
  f x p i | i < (dy' + 1) = do
    (x2,p2) <- f2 x p i 
    f x2 p2 (i + 1)
  f _ _ _ = return ()
  f2 x p i = do
    -- traceShowM $ "VIndex: " ++ (show (x,y0 + i))
    a0 <- readArray (coask wa) (x, y0 + i)
    writeArray (coask wa) (x, y0 + i) ((extract wa) a0)
    if p >= 0
      then return (x+dir,p- 2*dy')
      else return (x, p + 2 * dx)
  in if dy' /= 0 
    then f x0 (2*dx - dy') 0
    else return ()

adjCoDrowLineH ::
  ( Comonad w
  , Ix x
  , Real x
  , MArray TArray a STM
  , Show x
  ) =>
  (x,x) ->
  (x,x) ->
  W.AdjointT
    (AdjArrayL (x,x) a)
    (AdjArrayR (x,x) a)
    w
    (a -> a) ->
  STM ()
adjCoDrowLineH ((x0' :: x),y0') (x1',y1') wa = let
  (x0,x1) = if x0' > x1' then (x1',x0') else (x0',x1')
  (y0,y1) = if x0' > y1' then (y1',y0') else (y0',y1')
  dx = x1 - x0
  dy' = y1 - y0
  dir = if dy' < 0 then (-1) else 1
  dy = dy' * dir
  f y p i | i < (dx+1) = do
    (y2,p2) <- f2 y p i
    --traceShowM $ "f: " ++ (show i )
    f y2 p2 (i+1)
  f _ _ _ = return ()
  -- f2 :: (MArray TArray a STM) => x -> x -> x -> STM (x,x)
  f2 y p i = do
    -- traceShowM $ "Points: " ++ (show (x0',y0')) ++ " " (show (x1',y1'))
    --traceShowM $ "HIndex: " ++ (show (x0+i, y))
    a0 <- readArray (coask wa) (x0+i, y)   
    writeArray (coask wa) (x0+i, y) ((extract wa) a0)
    --traceShowM $ "Post writeArray"
    --traceShowM $ "y: " ++ (show y)
    --traceShowM $ "p: " ++ (show p)
    if p >= 0
      then do
        --traceShowM $ "return1: " ++ (show (y+dir,p-2*dx))
        return (y+dir,p- 2*dx)
      else do
        --traceShowM $ "return2: " ++ (show (y, p+2*dy))
        return (y, p + 2 * dy)
  in if dx /= 0
    then do
      f y0 (2*dy - dx) 0
    else return ()
  
adjCoDrowLine :: 
  ( Comonad w
  , Ix x
  , Real x
  , Show x
  ) =>
  (x,x) ->
  (x,x) ->
  W.AdjointT
    (AdjArrayL (x,x) a)
    (AdjArrayR (x,x) a)
    w
    (a -> a) ->
    a0 <- readArray (coask wa) (x, y0 + i)
  STM ()
adjCoDrowLine p0@(x0,y0) p1@(x1,y1) wa =
  if abs (x1 - x0) > abs (y1 - y0)
    then adjCoDrowLineH p0 p1 wa
    else adjCoDrowLineV p0 p1 wa

adjCoDrowLineConst p0 p1 wa = adjCoDrowLine p0 p1 (fmap const wa) 

cube :: Picture
cube = Polygon [(0,0),(1,0),(1,1),(0,1),(0,0)]

adjCoDrowArray :: 
  ( Comonad w
  , Real x
  , Ix x
  ) =>
  (a -> Picture) ->
  W.AdjointT 
    (AdjArrayL (x,x) a)
    (AdjArrayR (x,x) a)
    w 
    b ->
  STM Picture
adjCoDrowArray f w = do
  lip <- getAssocs (coask w)
  return $ Pictures $ fmap (\((x,y),a)-> Translate (realToFrac x) (realToFrac y) $ f a ) lip

class HasMapVarT i a where
  mapVarTBool :: Lens' a (Map i (TVar Bool, Set i))

class HasNeiron a where
  neiron :: Lans' a (TVar Bool)

initNeiron :: 
  ( Ix i
  , HasMapVarT i a
  , HasNeiron a
  ) =>
  a ->
  (i,i) ->
  (i,i) ->
  IO (TArray (i,i) a)
initNeiron a0 p0 p1 = do
  let li = range p0 p1
  la <- mapM (\i-> do
    tvN <- newTVarIO False
    return ((set mapVarTBool empty . set neiron tvN) a0)
    ) li
  newListArray (p0,p1) la

type CxtAxon i w a g = 
  ( Comonad w
  , Ix i
  , HasMapVarT (i,i) a
  , HasNeiron a
  , Random i
  , RandomGen g
  )

type NeirobPoint i = (i,i)

lineAxon1 ::
  ( CxtAxon i w a g
  ) =>
  NeironPoin i ->
  (i,i) ->
  (i,i) ->
  W.AdjoinT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b
  -> STM ()
lineAxon1 pn p0 p1 w = do
  let arr = coask w
  an <- readArray arr pn
  let tvAxonN = an^.neiron
  adjCoDrowLine p0 p1 (fmap (const (\ a-> let
    mapTV = a^.mapVarTBool
    in set mapVarTBool (insert pn (tvAxonN, empty)) a
    )) w)

randomAxon :: 
  ( CxtAxon i w a g
  ) =>
  NeironPoint i ->
  (i,i) ->
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR) (i,i) a)
    w
    b
  -> IO (i,i)
randomAxon pn p0 p1 w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr -- ???
  if not $ p0 >= xpi && p1 <= ypi then error "randomAxon index bound error"
    else do
      rpi <- randomRIO (p0,p1)
      atomically $ lineAxon1 pn pn rpi w
      return rpi

randomAxoninBox ::
  ( CxtAxon i w a g
  ) =>
  NeironPoint i ->
  i ->
  W.AsjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b -> 
  IO (i,i)
randomAxonBox np@(xn,yn) r w = do
  let arr = coask w
  let p0@(x0,y0) = (xn - r, yn - r)
  let p1@(x1,y1) = (xn + r, yn + r)
  ppi@(xpi,ypi) <- getBounds arr -- ???
  if p0b = if p0 >= xpi && p0 <= ypi then p0 else xpi
  if p1b = if p1 >= xpi && p1 <= ypi then p1 else ypi
  randomAxon np p0b p1b w

initAxonForNeironBox ::
  ( CxtAxon i w a g
  ) =>
  i ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b -> 
  IO [(NeironPoint,(i,i))]
initAxonForNeironBox r w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  let allN = range ppi
  mapConcurrently (\i->do
    ia <- randomAxonBox i r w
    return (i,ia)
    ) allN

type ChanceAxon = Int

randomRSTM :: 
  ( RandomGen g
  , Random a
  ) =>
  TVar g ->
  (a,a) ->
  STM a
randomRSTM tvg pa -> do
  g <- readTVar tvg
  let (a,ng) = randomR pa g
  writeTVar tvg ng

axogenesPoint :: 
  ( CxtAxon i w a g 
  ) =>
  TVar g ->
  (i,i) ->
  ChanceAxon ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b
  -> STM ()
axogenesPoint tvg p@(x,y) ca w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then error "axogenesPoint: index out of bounds in array"
    else do
      cha <- randomRSTM tvg (0,ca)
      if cha /= 0 then return ()
        else do
	  ae <- readArray arr p
	  let mapA = ae^.mapVarTBool
	  let lk = keys mapA
	  let ll = length lk
	  if ll > 1 then return () 
	    else do 
	      ril0 <- randomRSTM tvg (1,ll)
	      ril1 <- randomRSTM tvg (1,ll)
	      if ril0 == ril1 then return ()
	        else do
		writeArray arr p (set mapVarTBool (adjust (\(tvb,seti)-> (tvb, insert (lk ! ril1) seti) ) (lk ! ril0) mapA) ae)  
              
updateAxogenesPoint ::
  ( Cxt i w a g
  ) =>
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b -> 
  STM ()
updateAxogenesPoint p w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then error "updateAxogenesPoint: index out of bounds"
    else do
      ae <- readArray arr p
      let mapA = ae^.mapVarTBool
      traverseWithKey (\ pk@(xk,yk) (tvbool, sp) -> do
        traverse_ (\ pset -> do
	    boolAxon <- readTVar tvbool
	    let mtvbool2sp2 = lookup pset mapA
	    mapM (\ (tvbool2,sp2) -> do
	      writeTVar tvbool2 boolAxon
	      ) mtvbool2sp2
	  ) sp
	) mapA

clearNeironPoint ::
  ( Cxt i w a g
  ) =>
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  STM ()
clearNeironPoint p w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then error "updateAxogenesPoint: index out of bounds"
    else do
      ae <- readArray arr p
      let tvneir = ae^.neiron
      writeTVar tvneir False

clearAxoginesPoint ::
  ( Cxt i w a g
  ) =>
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  STM ()
clearAxoginesPoint p w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then error "updateAxogenesPoint: index out of bounds"
    else do
      ae <- readArray arr p
      let mapA = ae^.mapVarTBool
      traverseWithKey (\ pk@(xk,yk) (tvbool, sp) -> do
        writeTVar tvbool False
	) mapA
 


