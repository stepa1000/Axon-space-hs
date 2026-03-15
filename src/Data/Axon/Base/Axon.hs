{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.Axon where

imprt Prelude as P

import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM.TArray
import Control.Core.Composition
import Control.Base.Comonad
import Graphics.Gloss.Data.Picture
import Graphics.Gloss.Data.Color
import Data.Ix
import Data.Functor.Adjunction
import Control.Comonad
import Control.Comonad.Env
import Control.Monad.Reader
import Control.Comonad.Trans.Adjoint as W
import Data.Array.MArray
import Debug.Trace
import Control.Lens
import System.Random
import Data.Map as Map
imoprt Data.HashMap.Lazy as HMap
import Data.Set as Set
import Data.HashSet as HSet
import Control.Concurrent.Async
import Data.Traversable
import Data.Foldable
import Data.Proxy
import Data.UUID
import Data.Sequence as Seq

-- Array

type AdjArrayL i a = Env (TArray i a)

type AdjArrayR i a = Reader (TArray i a)

-- | 
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
    -- a0 <- readArray (coask wa) (x, y0 + i)
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
  mapVarTBool :: Lens' a (Map.Map i (TVar Bool, Set.Set i))

class HasNeiron a where
  neiron :: Lens' a (TVar Bool)

initNeiron :: 
  ( Ix i
  , HasMapVarT i a
  , HasNeiron a
  ) =>
  a ->
  (i,i) ->
  (i,i) ->
  IO (TArray (i,i) a)
initNeiron a0 (p0 :: (i,i)) p1 = do
  let li = range (p0,p1)
  la <- mapM (\i-> do
    tvN <- newTVarIO False
    return ((set (mapVarTBool @i @_) Map.empty . set neiron tvN) a0)
    ) li
  newListArray (p0,p1) la

type CxtAxon i w a g = 
  ( Comonad w
  , Ix i
  , HasMapVarT (i,i) a
  , HasNeiron a
  , Random i
  , RandomGen g
  , Real i
  , Num i
  , Ord i
  , Show i
  , Show a
  )

type NeironPoint i = (i,i)

lineAxon1 ::
  ( CxtAxon i w a g
  ) =>
  Proxy g ->
  NeironPoint i ->
  (i,i) ->
  (i,i) ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b
  -> STM ()
lineAxon1 pyx pn p0 p1 w = do
  let arr = coask w
  an <- readArray arr pn
  let tvAxonN = an^.neiron
  adjCoDrowLine p0 p1 (fmap (const (\ a-> let
    mapTV = a^.mapVarTBool
    in set mapVarTBool (Map.insert pn (tvAxonN, Set.empty) mapTV) a
    )) w)

randomAxon :: 
  ( CxtAxon i w a g
  ) =>
  Proxy g ->
  NeironPoint i ->
  (i,i) ->
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b
  -> IO (i,i)
randomAxon (pxy :: Proxy g) pn p0 p1 w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr -- ???
  if not $ p0 >= xpi && p1 <= ypi then error "randomAxon index bound error"
    else do
      rpi <- randomRIO (p0,p1)
      atomically $ lineAxon1 pxy pn pn rpi w
      return rpi

randomAxoninBox ::
  ( CxtAxon i w a g
  ) =>
  Proxy g ->
  NeironPoint i ->
  i ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b -> 
  IO (i,i)
randomAxoninBox (pxy :: Proxy g) np@(xn,yn) r w = do
  let arr = coask w
  let p0@(x0,y0) = (xn - r, yn - r)
  let p1@(x1,y1) = (xn + r, yn + r)
  ppi@(xpi,ypi) <- getBounds arr -- ???
  let p0b = if p0 >= xpi && p0 <= ypi then p0 else xpi
  let p1b = if p1 >= xpi && p1 <= ypi then p1 else ypi
  randomAxon pxy np p0b p1b w

initAxonForNeironBox ::
  ( CxtAxon i w a g
  ) =>
  Proxy g -> 
  i ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b -> 
  IO [(NeironPoint i,(i,i))]
initAxonForNeironBox pyx r w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  let allN = range ppi
  mapConcurrently (\i->do
    ia <- randomAxoninBox pyx i r w
    return (i,ia)
    ) allN

type ChanceAxon = (Int,Int)

randomRSTM :: 
  ( RandomGen g
  , Random a
  ) =>
  TVar g ->
  (a,a) ->
  STM a
randomRSTM tvg pa = do
  g <- readTVar tvg
  let (a,ng) = randomR pa g
  writeTVar tvg ng
  return a

initAxogenesPoint :: 
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
initAxogenesPoint tvg p@(x :: i,y) (minca,ca) w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then error "axogenesPoint: index out of bounds in array"
    else do
      cha <- randomRSTM tvg (0,ca)
      if cha <= minca then return ()
        else do
	  ae <- readArray arr p
	  let mapA = ae^.(mapVarTBool @(i,i))
	  let lk = keys mapA
	  let ll = length lk
	  if ll > 1 then return () 
	    else do 
	      ril0 <- randomRSTM tvg (1,ll)
	      ril1 <- randomRSTM tvg (1,ll)
	      if ril0 == ril1 then return ()
	        else do
		writeArray arr p 
		   ( set 
		        (mapVarTBool @(i,i)) 
			( adjust 
			     (\(tvb,seti)-> (tvb, Set.insert (lk !! ril1) seti) ) -- Maybe all order, nit ine side
			     (lk !! ril0) 
			     mapA) 
			ae)  

allAxogenesPoint :: 
  ( CxtAxon i w a g 
  ) =>
  TVar g ->
  ChanceAxon ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b
  -> IO ()
allAxogenesPoint tvg ca w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  let allN = range ppi
  mapConcurrently (\i->do
    ia <- atomically $ initAxogenesPoint tvg i ca w
    return (i,ia)
    ) allN

updateAxogenesPoint ::
  ( CxtAxon i w a g
  ) =>
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b -> 
  STM ()
updateAxogenesPoint (p :: (i,i)) w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then error "updateAxogenesPoint: index out of bounds"
    else do
      ae <- readArray arr p
      let mapA = ae^.(mapVarTBool @(i,i))
      _ <- traverseWithKey (\ pk@(xk,yk) (tvbool, sp) -> do
         boolAxon <- readTVar tvbool
         setBool <- foldlM (\ () pset -> do -- pset
	    -- boolAxon <- readTVar tvbool
	    let mtvbool2sp2 = Map.lookup pset mapA
	    bool2 <- fmap (maybe False id) $ mapM (\ (tvbool2,sp2) -> do
	      bool2 <- readTVar tvbool2
	      if boolAxon 
	         then do 
		    writeTVar tvbool2 boolAxon
		    return bool2
		 else return bool2
	      ) mtvbool2sp2
	    return bool2 -- (snd mtvbool2sp2)
         -- return undefined
	    ) () sp
	 let reBool = foldl || False setBool
	 writeTVar tvbool reBool
	) mapA
      return ()

clearNeironPoint ::
  ( CxtAxon i w a g
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
  ( CxtAxon i w a g
  ) =>
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  STM ()
clearAxoginesPoint (p :: (i,i)) w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then error "updateAxogenesPoint: index out of bounds"
    else do
      ae <- readArray arr p
      let mapA = ae^.(mapVarTBool @(i,i))
      _ <- traverseWithKey (\ pk@(xk,yk) (tvbool, sp) -> do
        writeTVar tvbool False
	) mapA
      return ()

updateIn2Box ::
  ( Comonad w-- CxtAxon i w a g
  , Ix i
  ) =>
  Float -> -- ???? Int
  Float -> -- ????? Int
  (i,i) ->
  ( (i,i) -> 
    W.AdjointT
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
    STM ()
  ) ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  IO ()
updateIn2Box r1' r2' p f w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  -- (x - x0)^2 + (y - y0)^2 = r^2
  let r1 = if r1' > r2' then r2' else r1'
  let r2 = if r1' > r2' then r1' else r2'
  let intr2 = round r2-- fromIntegral r2
  let intr1 = round r1-- fromIntegral r1 -- r1 < r2
  let (xb1,yb1) = xpi
  let (xb2,yb2) = ypi -- xpi < ypi ???????!!!!!!!!!!!!
  let (x0,y0) = p
  let rw = rangeSize (y0,yb2)
  let rd = rangeSize (x0,xb2)
  let rs = rangeSize (yb1,y0)
  let ra = rangeSize (xb1,x0)
  let vrw = rw - intr2
  let vrd = rd - intr2
  let vrs = rs - intr2
  let vra = ra - intr2
  let xr2 = if vrd < 0 then xb2 else ((range (x0,xb2)) !! intr2)
  let ys2 = if vrs < 0 then yb1 else ((range (yb1,y0)) !! intr2)
  let xl2 = if vra < 0 then xb1 else ((range (xb1,x0)) !! intr2)
  let yw2 = if vrw < 0 then yb2 else ((range (y0,yb2)) !! intr2)
  -- sqrt (x + y) = r => x^2 + y^2 = r^2
  -- 2*a^2 = r^2
  -- a^2 = (r^2) / 2
  -- a = sqrt ((r^2) / 2)
  let a = round $ sqrt (fromIntegral $ quot (intr1^2) 2)
  let vrw2 = rw - a
  let vrd2 = rd - a
  let vrs2 = rs - a
  let vra2 = ra - a
  let yw1 = if vrw2 < 0 then yb2 else ((range (y0,yb2)) !! a)
  let xr1 = if vrd2 < 0 then xb2 else ((range (x0,xb2)) !! a)
  let ys1 = if vrs2 < 0 then yb1 else ((range (yb1,y0)) !! a)
  let xl1 = if vra2 < 0 then xb1 else ((range (xb1,x0)) !! a)
  let dyyw = range (yw1,yw2)
  let dxxd = range (xr1,xr2)
  let dyys = range (ys1,ys2)
  let dxxa = range (xl1,xl2)
  let pwwd = liftA2 (,) (range (x0,xr1)) dyyw
  let pwwdd = liftA2 (,) dxxd dyyw
  let pwdd = liftA2 (,) dxxd (range (y0,yw1))
  let psdd = liftA2 (,) dxxd (range (ys1,y0))
  let pssdd = liftA2 (,) dxxd dyys -- ????????
  let pssd = liftA2 (,) (range (x0,xr1)) dyys
  let pssa = liftA2 (,) (range (xl1,x0)) dyys
  let pssaa = liftA2 (,) dxxa dyys
  let psaa = liftA2 (,) dxxa (range (ys1,y0))
  let pwaa = liftA2 (,) dxxa (range (y0,yw1))
  let pwwaa = liftA2 (,) dxxa dyyw
  let pwwa = liftA2 (,) (range (xl1,x0)) dyyw
  let in2BS = pwwd ++ pwwdd ++ pwdd ++ psdd ++ pssdd ++ pssd ++ pssa ++ pssaa ++ psaa ++ pwaa ++ pwwaa ++ pwwa
  forConcurrently_ in2BS (\i-> do
    atomically $ do
      f i w
    )

redredin2Box :: 
  (Int, Int) ->
  W.AdjointT
    (AdjArrayL (Int,Int) Picture)
    (AdjArrayR (Int,Int) Picture)
    Identity
    () ->
  STM ()
redredin2Box p w = do
  let arr = coask w
  writeArray arr p (Color red $ cube)

-- instance HasMapVarT 

updateIn2BoxRedPic ::
  Float ->
  Float ->
  (Int,Int) ->
  W.AdjointT
    (AdjArrayL (Int,Int) Picture)
    (AdjArrayR (Int,Int) Picture)
    Identity
    () ->
  IO ()
updateIn2BoxRedPic r1 r2 p w = do
  updateIn2Box r1 r2 p redredin2Box w

updateIn2Radius :: 
  ( Comonad w-- CxtAxon i w a g
  , Ix i
  ) =>
  Float -> -- ???? Int
  Float -> -- ????? Int
  (i,i) ->
  ( (i,i) -> 
    W.AdjointT
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
    STM ()
  ) ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  IO ()
updateIn2Radius r1 r2 p0@(x0,y0) f w = do
  updateIn2Box r1 r2 p0
    (\ ip@(xi,yi) w -> do
      let rv = abs (xi - x0) + abs (yi - y0) 
      if (rv > (round r1)) && (rv < (round r2)) 
        then do
	  f ip w
	else return ()
    ) 
    w

updateIn2RUpAxogenesPoint :: 
  ( Comonad w-- CxtAxon i w a g
  , Ix i
  ) =>
  Float -> -- ???? Int
  Float -> -- ????? Int
  (i,i) ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  IO ()
updateIn2RUpAxogenesPoint r1 r2 p0 w = 
   updateIn2Radius r1 r2 p0 updateAxogenesPoint w


updateIn2RUpClearAxoginesPoint r1 r2 p0 w = 
   updateIn2Radius r1 r2 p0 clearAxoginesPoint w

waveInterval ::
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   ) => 
   Float ->
   (i,i) ->
   ( Float ->
     Float ->
     (i,i) ->
     W.AdjointT 
        (AdjArrayL (i,i) a)
        (AdjArrayR (i,i) a)
        w
        b ->
     IO ()
   ) -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
waveInterval rA p0 f w = do
   let arr = coask w
   ppi@(xpi,ypi) <- getBounds arr 
   let arrR = sqrt ((fromIntegral xpi) ^ 2 + (fromIntegral ypi) ^ 2) 
   let l1 = [0,rA .. arrR]
   let l2 = [rA, rA * 2 .. arrR]
   mapM (\(x,y) -> f x y p0 w) (zip l1 l2) 

updateDedritSpace :: -- GOOD abstract the
  ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   ) => 
   Float ->
   [(i,i)] ->
   ( W.AdjointT 
        (AdjArrayL (i,i) a)
        (AdjArrayR (i,i) a)
        w
        b ->
     IO ()
    ) ->
    W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () 
updateDedritSpace s li f w = do
  forConcurrently_ li (\i-> do
    waveInterval s i updateIn2RUpAxogenesPoint w 
    )
  -- waveInterval s i updateIn2RUpAxogenesPoint w
  f w
  waveInterval s (head li) updateIn2RUpClearAxoginesPoint w -- all array to false maybe ?????????!!!!!!!!!!!
   
upIn2RUpAxoginesPWave rA p0 w = waveInterval rA p0 updateIn2RUpAxogenesPoint 

type DendritPatern i = Set (i,i)

generateDendritPatern :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) => 
   TVar g ->
   (i,i) ->
   i ->
   Int -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   STM (DendritPatern i)
generateDendritPatern g p0@(px,py) r w k = do
   let arr = coask w
   ppi@(xpi,ypi) <- getBounds arr
   if not $ and [(px - r, py - r) >= xi, (px + r, py + r) <= yi] 
      then error "updateAxogenesPoint: index out of bounds" 
      else do
         let pxA = px - r
	 let pyA = py - r
	 let pxB = px + r
	 let pyB = py + r
	 fmap fold $ mapM (\i-> do
            p <- randomRSTM g ((pxA,pyA),(pxB,pyB))
            return $ Set.singleton p
	    ) (0..k)
         
writeDendritPatern :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) => 
   DendritPatern i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   STM ()
writeDendritPatern dp w = do
   let arr = coask w
   ppi@(xpi,ypi) <- getBounds arr
   mapM (\ i -> 
      a <- readArray arr i 
      tvBool <- a^.neiron
      writeTVar tvBool true  
      ) dp
   
readDendritPatern :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) => 
   -- DendritPatern i ->
   (i,i) ->
   i -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   STM (DendritPatern i)
readDendritPatern (x,y) r w = do
   let arr = coask w
   ppi@(xpi,ypi) <- getBounds arr
   foldlM (\ bn i -> 
      if inRange ppi i 
         then do
            a <- readArray arr i 
            tvBool <- a^.neiron
            b <- readTVar tvBool true
            return $ bn <> (Set.singleton i)
	 else return $ Set.empty
      ) Set.empty (range (x-r,y-r) (x+r,y+r))

midleDP :: Num i => DendritPatern i -> (i,i)
midleDP dp = f $ fold $ map (\(x,y)-> (Max x,Min x, Max y, Min y)) dp
   where
      f (maxX,minX,maxY,MinY) = ((maxX - minX / (realToFrac 2)) + minX ,(maxY - minY / (realToFrac 2)) + minY )

type QueueWriteDP i = TQueue [DendritPatern i]

type QueueReadDP i = TQueue [(DendritPatern i,(i,i))] -- (i,i)

type PointAndR i = ((i,i),i)

type WaveStep = Float 

dendritWriteRead ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   WaveStep ->
   QueueWriteDP i ->
   QueueReadDP i ->
   [PointAndR i] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
dendritWriteRead s quW quR lP w = do
   lldp <- atomicaly $ flushTQueue quW 
   let lldpp = (fmap . fmap) (\dp-> (dp, midleDP dp)) lldp
   mapM (\ldpp-> do
      mapM (\(dp,_)-> writeDendritPatern dp w) ldpp
      updateDedritSpace s (fmap snd ldpp) 
         ( \ wn -> do
	    ldpOut <- mapM (\ (ip,i) -> do
	       dpn <- readDendritPatern ip r
	       return (dpn,ip)
	       ) lP
	    atomicaly $ writeTQueue quR ldpOut
	 ) w
      ) lldpp

type PointLinearMemory i = PointAndR i 

type QueuePLM i = TQueue (PointLinearMemory i)

type SeqLM i = Seq (DendritPatern i, PointAndR i)

dendritLinearMemory ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   TVar (SeqLM i) ->
   WaveStep ->
   QueueWriteDP i ->
   -- QueueReadDP i ->
   QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
dendritLinearMemory tvsDP s quW quPLM w =
   lPLM <- atomicaly $ flushTQueue quPLM
   lldp <- atomicaly $ flushTQueue quW
   mapM (\ (plm,ldp) -> do
      quWdp <- newTQueueIO 
      quRdp <- newtQueueIO
      atomivaly $ do
         writeTQueue quWdp ldp
	 -- writeTQueue quRdp
      dendritWriteRead s quWdp quRdp [plm] w
      atomicaly $ do
         lrdp <- flushTQueue quRdp
         modifyTVar tvsDP (\sdp-> sdp :>| (head lrdp)) -- plm
      ) $ zip lPLM lldp
   
 
dendritReactLinearMemory ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   SeqLM i -> -- TVar (SeqLM i) ->
   WaveStep ->
   QueueWriteDP i ->
   QueueReadDP i ->
   -- QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (Seq Bool)
dendritReactLinearMemory sdpp s quW quR w =
   -- sdpp <- readTVarIO tvsDP 
   let lpr = fold $ fmap ( (: []) . snd) sdpp
   dendritWriteRead s quW quR lpr w
   seqrdp <- fmap (foldl (\ b a -> b :>| (fold $ fmap HSet.singletone a)) Seq.empty) $ atomicaly $ flushTQueue quRdp
   return $ Seq.zipWith (\ (dp,pr) hsDp -> HSet.member (dp,pr) hsDp) sdpp seqrdpfoldl

type HMDPf i = HashMap (DendritPatern i, PointAndR i) Int 

-- frequncy generalization for reception

frequencyLinearMemoryHMDP :: SeqLM i -> HMDPf i
frequencyLinearMemoryHMDP slm = fmap getSum $ foldl1 (unionWith (<>)) $ fmap (\(dp,pr)-> HMap.singletone (dp,pr) (Sum 1) ) slm

type MFDP i = Map Int (HeshSet (DendritPatern i, PointAndR i))

frequencyLMMF :: HMDPf i -> MFDP i
frequencyLMMF hmdpf = foldl1 (Map.unionWith (<>)) $ HMap.mapWithKey (\ k fr -> Map.singletone fr (HSet.singletone k)) hmdpf

seqToFrequency :: SeqLM i -> MFDP i 
seqToFrequency = frequencyLMMF . frequencyLinearMemoryHMDP 

type PatternRadius = Int

generationPattern :: PatternRadius -> SeqLM i -> HashSet (SeqLM i)
generationPattern pr slm = hsslm 
   where
      hsslm = foldl1 (<>) $ map (i->let
         li = [ x | x >= 0, x < (Seq.length slm), x <- [i-pr, i-pr +1 .. i+pr]]
         in HSet.singletone $ foldl1 (<>) $ map (\j-> Seq.singletone (index slm j)
	    ) li
	 ) lei
      lei = join $ map (\dppr@(dp,pointR)-> let
         in Seq.elemIndicesR slm dppr
	 ) lfreMidleMax
      mfre = seqToFrequency slm
      mmaxFre = Map.lookupMax mfre
      lfreMidleMax = join $ maybeToList $ map (\(k,a)-> let
         midK = k / 2 -- maybe 80/20, 20/80 Pareto. The parametor
	 in fold $ fmap (\x->[x]) $ Map.filterKeys (\nk-> nk > midK) mfre
	 ) mmxaFre

distanceSeqLM :: SeqLM i -> SeqLM i -> Float
distanceSeqLM slm1 slm2 = d / ml
   where
      ml = realToFrac $ max (Seq.length slm1) (Seq.length slm2) 
      d = getSum $ fold $ seq.zipWith (\x y -> if x == y then Sum 1 else Sum 0) slm1 slm2

type GeneralSeqLM i = SeqLM i 

type SpecialHSSeqLM i = HashSet (SeqLM i)

type GeneralRadius = Float

generalizationPattern :: GeneralRadius -> HashSet (SeqLM i) -> (SeqLM i,SpecialHSSeqLM i, HashSet (SeqLM i))
generalizationPattern gr hsslm = (gslm,shsseqLM,zhsslm)
   where
      (shsseqLM, zhsslm) = HSet.partition (\slm-> (distanceSeqLM slm gslm) > gr ) hsslm
      gslm = foldl1 (\ (d1,slm1) (d2,slm2) -> if d1 > d2 then (d1,slm1) else (d2,slm2)) ldslm
      ldslm = fmap (\slm1-> let
         ad = foldl1 (+) $ fmap (\slm2 -> distanceSeqLM slm1 slm2) hsslm
	 in (ad / (realToFrac $ Seq.length hsslm), slm1)
	 ) $ HSet.toList hsslm

-- end frequncy generalization for reception
-- Pattern for pattern exist for reception, but not for liniar memorym because linear memory is uneq patern for eny reception
--
-- type SeqR i = SeqLM i
type SeqR i = Seq (HashSet (DendritPatern i, PointAndR i) )

readReception ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   WaveStep ->
   -- QueueWriteDP i ->
   SeqLM i ->
   [PointAndR i] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (SeqR i)
readReception ws seqLM lpr w = do
   quWdp <- newTQueueIO 
   quRdp <- newtQueueIO 
   mapM (\ dppr -> do 
      atomicaly $ writeTQueue quWdp (fst dppr)
      ) seqLM
   dendritWriteRead ws quWdp quRdp lpr w
   seqrdp <- fmap (foldl (\ b a -> b :>| (fold $ fmap HSet.singletone a)) Seq.empty) $ atomicaly $ flushTQueue quRdp 
   return seqrdp 

type Reception i = HashSet (DendritPatern i, PointAndR i) 

type ReceptionBind i = HashMap (HashSet (DendritPatern i, PointAndR i)) (DendritPatern i, PointAndR i, Int)

type ReceptionBind_A i = HashMap (HashSet (DendritPatern i, PointAndR i)) [Int]

indexedSeq i = Seq.iterateN i (+ 1) 0 

receptionBind_A ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   WaveStep ->
   -- QueueWriteDP i ->
   SeqLM i ->
   [Reception i] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (ReceptionBind_A i)
receptionBind_A ws seqLM lr w =
   quWdp <- newTQueueIO 
   quRdp <- newtQueueIO
   fmap foldl $ mapM (\hsdppr->do
      atomicaly $ writeTQueue quWdp $ fmap (fst) $ HSet.toLisst hsdppr
      seqBool <- dendritReactLinearMemory seqLM ws quWdp quRdp w
      let sib = Seq.filter (\(i,b)->b) $ Seq.zip (indexedSeq $ Seq.length seqBool) seqBool
      return $ foldl (HMap.unionWith (<>)) (HMap.epmty) $ fmap (\(i,_)-> HMap.singletone hsdppr [i]) sib
      ) lr

type FrecuencyReception i = Map Int [(HashSet (DendritPatern i, PointAndR i))] -- Not emty and only one ???????
type IndexReception i = Map Int [(HashSet (DendritPatern i, PointAndR i))]

indexReception :: ReceptionBind_A i -> IndexReception i 
indexReception rba = foldl (Map.unionWith (<>)) (Map.empty) $ 
   mapWithKey (\ k li -> foldl (Map.unionWith (<>)) (Map.empty) $ fmap (\i-> Map.singletone i [k]) li) rba

frecuencyReception :: ReceptionBind_A i -> FrecuencyReception i 
frecuencyReception rba = foldl (Map.unionWith (<>)) (Map.empty) $ 
   mapWithKey (\ k li -> Map.singletone (P.length li) [k]) rba
