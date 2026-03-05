{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.Axon where

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

updateDedritSpace :: 
  ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   ) => 
   Float ->
   (i,i) ->
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
updateDedritSpace s i f w = do
  waveInterval s i updateIn2RUpAxogenesPoint w
  f w
  waveInterval s p updateIn2RUpClearAxoginesPoint w
   
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
         
class HasMemory a i where
  -- reactionTo :: [TArray Int (Maybe (DendritPatern i))] 
  rection :: Lens' a [TArray Int (Maybe (UUID,Set (DendritPatern i)))] 
  -- association :: Lens' a [Set (DendritPatern i)]
  --           Lens' a (TArray Int (Maybe (DendritPatern i)) <-> TArray Int (Maybe (UUID,DendritPatern i))) 
  -- spike :: Lens' a (TArray Int (Maybe (DendritPatern i)) -> TArray Int (Maybe (UUID,DendritPatern i)) )

type EitherPatern i = Either (DendritPatern i) (Set (DendritPatern i))

type AbstPatern a i = TArray Int (Maybe (UUID, EitherPatern i)) 

type CxtAxonMem i w a g = 
   ( CxtAxon i w a g
   , HasMemory a i 
   )
 
addReacrionDP :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   ) => 
--   TArray Int (Maybe (DendritPatern i)) ->
   Float ->
   TArray Int (Maybe (UUID,(DendritPatern i))) ->
   (i,i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   STM Bool
addReacrionDP s aTo pa w = do
   let arr = coask w
   ppi@(xpi,ypi) <- getBounds arr
   a <- readArray arr pa 
   let rea = a^.reaction
   limpt <- getAssocs aTo
   (Or b) <- mapM (\aimpt-> 
      -- limpt <- getAssocs aTo
      absA <- mapArray (fmap (\ (a,b) -> (a,Right b))) aimpt
      (And b) <- mapM (\ (i, muuiddp) -> do
        mept <- readArray absA i
	f ept ansA muuiddp i
	 ) limpt
      b1 <- getBounds aimpt
      b2 <- getBounds aTo
      if (b1 == b2) && b
         then do 
	    mapM (\(i,mpt)->do
	       bi <- getBounds aimpt
	       if inRange bi i
	          then do
	            c <- readArray aimpt i
		    let c2 = (\((uu,sptn))-> mpt >>= (\(uu2,pt)-> Just (uu,insert pt sptn) )) =<< c
	            writeArray aimpt i c2
		    return $ Or True
	          else return $ Or False
	    ) limpt
	 else return $ Or False  
      ) rea
   if (g limpt) && b
      then return b
      else do
         writeArray arr pa (set reaction (aTo : rea) a)
	 return b
   where
      g limpt = not $ length lpt == (size $ fold $ fmap Set.singleton lpt)
         where
	    lpt = join $ fmap (\(_,muupt)-> maybeToList muupt) limpt
      f Nothing _ Nothing _ = return $ And True
      f (uu,(Just (Right spt))) absA (Just (uu2,pt2)) j = do
         (_,y) <- getBounds absA
	 if y >= j then do
	    spt <- fmap fold $ mapM (\ i -> do
	      c <- readArray absA i 
	      (b,c2) <- case c of
	         Nothing -> return (True, Nothing)
	         (Just (uu3, Right spt3) ) -> return ((spt3 == spt) && (uu3 == uu) , Just (uu2,Left pt2))
	         (Just (uu3, Left pt3) ) -> return ((pt3 == pt2) && (uu3 == uu2) , Just (uu2,Left pt2))
	      writeArray absA i c2
	      return $ And b
	      else return $ And False -- Maybe False ????????????
	   ) (range (j,y))
	 return spt
      f (uu,(Just (Left pt))) absA (Just (uu2,pt2)) j = if pt == pt2 then return $ And True else return $ And False
      f _ _ _ _ = return $ And False
	
   -- mapArray aTo
   -- writeArray arr pa (set reaction (aTo : rea) a)
   {-aNil <- newArray (fromInteger 0, fromInteger 0) Nothing
   a <- readArray arr pa
   let fp = a^.reaction
   writeArray arr pa (set reaction (f fp) a)
   where
      f fp = 
         (\ aTl -> if aTl == aTo then aFrom else (biTo fp) aTl) :<->: 
         (\ aTu -> if aTu == aFrom then aTo else (biFrom fp) atu)  -}

sensPatern :: Float -> DendritPatern i -> DendritPatern i -> Bool
sensPatern s dp1 dp2 = (realToFrac x)/(realToFrac l) > s
   where
      (Sum x) = foldMap (\p-> if member p dp2 then Sum 1 else Sum 0) dp1
      l = max (size dp1) (size dp2)

distancePatern :: DendritPatern i -> DendritPatern i -> Int
distancePatern dp1 dp2 = x
   where
      (Sum x) = foldMap (\p-> if member p dp2 then Sum 1 else Sum 0) dp1

updateReactionDP ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   ) =>
   Float -> 
   TArray Int (Maybe (UUID, Set (DendritPatern i))) ->
   (i,i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   STM [TArray Int (Maybe (UUID,Set (DendritPatern i)))]
updateReactionDP s ta p w = do
   let arr = coask w
   ppi@(xp,yp) <- getBounds arr
   a <- readArray arr p
   let rea = a^.reaction 
   fmap catMaybes $ mapM (\ atn -> do
      ppi2@(xpi2,ypi2) <- getBounds atn 
      let latn = rangeSize ppi2
      ltn <- getAssocs atn
      lT <- fmap (getSum . fold) $ mapM (\ (i,muuidsdp) -> do
         muuiddp2 <- readArray ta i
	 return $ if maybe False id (f muuidsdp muuiddp2) then Sum 1 else Sum 0 -- False
	 ) ltn
      let t = (realToFrac lT)/(realToFrac latn)
      if t > s then return $ Just ltn
               else return Nothing
      ) rea
   where
      f Nothing Nothing = return True
      f m1 m2 = do
         uuiddp@(uu1,dp) <- m2
	 uuidsdp@(uu2,sdp) <- m1
	 return $ if (uu1 == uu2) && (not $ null $ filter (\ p -> member p dp) adp)
      f _ _ - Nothing
         

class HasUpdateMemory a i where
  -- reactionTo :: [TArray Int (Maybe (DendritPatern i))] 
  --updateStep :: Lens' a Int
  --updateStepLength :: Lens' a Int
  updateCurrentMemUp :: Lens' a [(Int,TArray Int (Maybe (UUID,Set (DendritPatern i))))]  
--                            Curent Step
--

midleDP :: Num i => DendritPatern i -> (i,i)
midleDP dp = f $ fold $ map (\(x,y)-> (Max x,Min x, Max y, Min y)) dp
   where
      f (maxX,minX,maxY,MinY) = ((maxX - minX / (realToFrac 2)) + minX ,(maxY - minY / (realToFrac 2)) + minY )

type FreeSpace = TVar Bool

seeDendrit ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , HasUpdateMemory a i
   ) =>
   Float -> -- step wave Dendrit space
--   w () ->
   ( DendritPatern i ->
     UUID ->
     Bool ->
     W.AdjointT 
        (AdjArrayL (i,i) a)
        (AdjArrayR (i,i) a)
        w
        b ->
     IO ()
   ) -> 
   [(i,i)] -> -- updating
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
--   FreeSpace -> 
--   UUID -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
seeDendrit ts f lu hma w = do
   let arr = coask w
   mapM (\ p ->
      a <- readArray arr p 
      let lupt = a^.updateCurrentMemUp 
      lupt2 <- fmap join mapM (\ (cs,apt) -> do
         muusdp <- readArray apt cs
	 mapM_ (\ (uu,sdp) ->
	    let mnarr = HMap.lookup uu hma
	    mapM_ (\(narr,fs)-> do
	       let wn = adjEnv narr (lower w)
	       atomicaly $ do
	          b <- readTaVar fs
                  -- b2 <- readTaVar fs2
		  check b 
		  writeTVar fs False
	       mapM_ (\ dp -> do
	          atomicaly $ writeDendritPatern dp wn
                  updateDedritSpace st (midleDP dp) (f dp uu False wn)
		  ) sdp
	       -- f (Set.empty) uu True wn
	       atomicaly $ writeTVar fs True
	       ) mnarr
	    ) muusdp
         ppi@(xp,yp) <- getBounds apt -- arr ???????????
	 return $ if inRange ppi (s+1) then [(s+1,apt)] else []
	 ) lupt
      writeArray arr p (set updateCurrentMemUp lupt2 a)
      ) lu

seeDendritALL ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , HasUpdateMemory a i
   ) =>
   Float ->
   w () ->
   ( DendritPatern i ->
     UUID ->
     Bool ->
     W.AdjointT 
        (AdjArrayL (i,i) a)
        (AdjArrayR (i,i) a)
        w
        b ->
     IO ()
   ) -> 
   HashMap UUID [(i,i)] -> -- updating
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
   IO ()
seeDendritALL s f w0 hup hta = do
   mapConcurrently_ (\ (uu,(ta,_)) -> 
      let wn = adjEnv ta w0 
      let lp = join $ maybeToList $ HMap.lookup uu hup 
      seeDendrit s f lp hta wn
      -- f (Set.empty) uu True wn
      ) (toList hta)
   mapConcurrently_ (\ (uu,(ta,_)) ->
      let wn = adjEnv ta w0 
      f (Set.empty) uu True wn
      ) (toList hta) 

class SensDendrit a i where
   sensD :: Lens' a (TArray Int (Maybe (UUID, Set (DendritPatern i))))
   nowSense :: Lens' a (Set (DendritPatern i))
   stepSense :: Lens' a Int
   maxStepSens :: Lens' a Int
   --sensePoint :: Lens' a (i,i)
   senseRadius :: Lens' a i

senseDendritRead ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   Float -> -- semi
   HashMap UUID (Set (i,i)) -> -- Read Active
   -- TQueue (UUID,DendritPatern i, (i,i)) ->
   HashMap UUID [(i,i)] -> 
   DendritPatern i ->
   UUID ->
--   Bool ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
senseDendritRead s ractive sensor ndp uu w = do
   let lp = join $ maybeToList $ HMap.lookup uu sensor
   mapM (\ p -> do
      let arr = coask w 
      a <- readArray arr p 
      dp <- readDendritPatern p (a^.senseRadius) w -- (a^.sensePoint)
      if dp == ndp then return ()
         else do
	    -- let sd = a^.sensD
	    let ns = a^.nowSense
	    writeArray arr p (set nowSense ((Set.singletone dp) <> ns) a)
	    --let msetAct = HMap.lookup uu ractive
	    --mapM (\setAct -> do
	    --   if Set.member p setAct
	    --      then atomicaly $ writeTQueue queRA (uu,dp,p)
	    --   ) msetAct
      ) lp

-- type BSuggestion = Bool

senseDendrit ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   Float -> -- semi
   HashMap UUID (Set (i,i)) -> -- Read Active
   TQueue (UUID,Set (DendritPatern i),(i,i) ) ->
   HashMap UUID [(i,i)] -> 
   DendritPatern i ->
   UUID ->
   Bool ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
senseDendrit s ractive _ sensor ndp uu False w = 
   senseDendritRead s ractive sensor ndp uu w  
senseDendrit s ractive queRA sensor ndp uu True w = do
   let lp = join $ maybeToList $ HMap.lookup uu sensor
   mapM (\ p -> do
      let arr = coask w 
      a <- readArray arr p 
      --dp <- readDendritPatern (a^.sensePoint) (a^.senseRadius) w
      --if dp == ndp then return ()
      --  else do
      let sd = a^.sensD
      let ns = a^.nowSense
      let i = a^.stepSense
      let mi = a^.maxStepSens
      let msetAct = HMap.lookup uu ractive
      mapM (\setAct -> do
         if Set.member p setAct
         then atomicaly $ writeTQueue queRA (uu,ns,p)
	 ) msetAct
      lipt <- getAssocs sd
      ppi@(xp,yp) <- getBounds sd
      nsd <- newArray_ (xp,i)
      mapM (\j-> do
	      if j == i
	         then if (not $ Set.nil ns) then writeArray nsd j (Just (uu,ns))
		         else writeArray nsd j Nothing 
		 else do
	            aj <- readArray sd j
	            writeArray nsd j aj
	      ) (if i <= mi then range (xp,i) else range (xp,mi))
      if i == mi 
         then do
	      ldp <- updateReactionDP s nsd p w
              arr0 <- newArray_ (0,0)
	      if length ldp > 0
	         then do
		    let bSetP = maybe False (\setP-> Set.member p setP) HMap.lookup uu ractive
                    if bSetP 
		       then do
		         writeArray arr p 
	                    ( ( set stepSense 0
	                        set nowSense Set.empty .
	                        set sensD arr0 . 
		                ) a) 
		       else do
	                  let ucmu = a^.updateCurrentMemUp
	                  let lr = filter (\e-> not $ elem e ldp) (a^.rection)	 
                          writeArray arr p 
	                     ( ( set stepSense 0
	                         set nowSense Set.empty .
	                         set sensD arr0 . 
		                 set updateCurrentMemUp (lr ++ ucmu)) a)
	         else do
	            let lr = (a^.rection) 
        	    if length lr < 0 
		       then do
		          writeArray arr p 
		             ( ( set stepSense 0 .
                                 set sensD arr0 .
                                 set nowSense Set.empty .
			         set reaction [nsd]
		             ) a) 
	               else writeArray arr p 
		            ( ( set stepSense 0 .
                                set sensD arr0 .
                                set nowSense Set.empty 
		              ) a) 
	 else do
	    writeArray arr p 
		    ( ( set stepSense (i + 1) .
                        set sensD nsd .
                        set nowSense Set.empty 
		        ) a) 
--      if Set.member p ractive
--         then return [ndp]
--	 else return []
      ) lp

data SuggestionSafe i = SuggestionSafe
   { safeSenseD :: (TArray Int (Maybe (UUID, Set (DendritPatern i)))) 
   , safeStepSense :: Int 
   , safeCurentMemUp :: [(Int,TArray Int (Maybe (UUID,Set (DendritPatern i))))]
   -- , safePoint :: (i,i)
   }

class Suggestion a i where
   safeSuggestion :: Lens' a (Cofree (HashMap [Signal i] ) (SuggestionSafe i))
   suggestionStart :: Lens' a Int
   -- safeMaxDepth :: Lens' a Int
   --

type SuggestionPath i = Seq (Set (Signal i))

suggestionSafe ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   -- [(UUID,(i,i))] ->
   [(i,i)] -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
suggestionSafe sp lpUp w = do
   let arr = coask w 
   mapM (\p-> do 
      a <- readArray arr p
      let ss = a^.suggestionStart
      let safeCo = g a (drop ss sp) $ a^.safeSuggestion 
      writeArray arr p (set safeSuggestion safeCo a)
      ) lpUp
   where
      g a (p:sp) sco@(b :< _) = if (HMap.nil fnsco) && (nil sp) -- ???? ||
            then b :< (HMap.insert p ((SuggestionSafe
	       (a^.senseD)
	       (a^.stepSense)
	       (a^.updateCurrentMemUp)
	       ) :< (HMap.empty)) fnsco)
	    else sco
	       {-(HMap.alter (\ mnsco -> (do 
	       nsco <- mnsco
	       return $ g sp nsco
	       ) <|> (
               return $ (SuggestionSafe
	          (a^.senseD)
	          (a^.stepSense)
	          (a^.updateCurrentMemUp)
	          ) :< (HMap.empty)
	       )
	       ) p fnsco)-}
         where
	    fnsco = unwrap sco
   
suggestionReSafe ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   Set (i,i)-> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
suggestionReSafe sp act lpUp w = do
   let arr = coask w 
   mapM (\p-> do 
      a <- readArray arr p
      let msugg = g sp $ a^.safeSuggestion 
      let ss = a^.suggestionStart
      mapM (\sugg-> do
         if length sp > ss 
	    then
               writeArray arr p (
	          ( set senseD (safeSenseD sugg) .
	            set stepSense (safeStepSense sugg) .
	            set updateCurrentMemUp (safeCurentMemUp sugg)
	          ) a)
	    else return ()
         ) msugg
      ) lpUp
   where
      g [] (o :< fsco) = return o
      g (p:sp) sco = (HMap.lookup p fnsco) >>= (\nsco-> g sp nsco)
         where
	    fnsco = unwrap sco

suggestionReSafeAll ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   HashMap UUID (Set (i,i)) -> 
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
   w () ->
   IO () -- [DendritPatern i]
suggestionReSafeAll spath act lpUp w0 =
   mapConcurrently_ (\ (uu,(ta,_)) -> 
      let wn = adjEnv ta w0 
      let sp = join $ maybeToList $ HMap.lookup uu act
      suggestionReSafe spath act wn
      ) lpUp

suggestionUpdate ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   [(i,i)] -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
suggestionUpdate sp ui w = do


activationD ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   [Signal i] -> -- Active
   HashMap UUID (TArray (i,i) a, FreeSpace) -> 
   IO ()
activationD lact hmTa = do
   mapM (\ (uu,sdp,p) -> do
      marr <- HMap.lookup uu hmTa
      mapM (\arr-> do
         a <- readArray arr p 
	 -- let r = a^.rection
	 -- let upR = a^.updateCurrentMemUp
	 narr <- newArray (0,0) (Just (uu,sdp))
         writeArray arr p (
	    ( set updateCurrentMemUp [(0,narr)] .
	      set maxStepSens 0
	    ) a
	    ) -- ((fmap (\x-> (0,x)) r) ++ upR))
	 ) marr
      ) lact

readActive :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   TQueue (Signal i) ->
   IO (HashMap (Signal i) (Sum Int ) )
readActive queue = do
   ls <- atomicaly $ flushTQueue queue
   return $ foldl (\ hm1 hm2 -> unionWith <> hm1 hm2) HMap.empty $ 
      fmap (\(uu,dp,pi) -> HMap.singletone (uu,dp,pi) (Sum 1) ) ls

type BSuggestion = Bool

dendritStepCycle' ::     
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , HasUpdateMemory a i
   ) =>
   Float -> -- step wave Dendrit space
   Float -> -- semi sense
   HashMap UUID (Set (i,i)) -> -- Read Active
   TQueue (UUID,DendritPatern i) ->
   HashMap UUID [(i,i)] -> -- Sense upda
   w () -> 
   HashMap UUID [(i,i)] -> -- updating
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
   IO ()
dendritStepCycle' stw semiS hmrAct quAct hmUpS w0 hmUpD hmArrFS = do
   seeDendritALL stw w0 
      ( senseDendrit semiS hmrAct quAct hmUpS
      ) hmUpD hmArrFS

type Signal i = (UUID, DendritPatern i, (i,i)) 

data DendritSC i a = DendritSC
   { stepWave :: Float
   , semiSense :: TVar Float
   , readActiveDSC :: HashMap UUID (Set (i,i))
   , queueActive :: TQueue (Signal i) 
   , sensorHM :: TVar (HashMap UUID (Set (i,i)) )
   , reactionHM :: TVar (HashMap UUID (Set (i,i)) )
   , fieldHM :: TVar (HashMap UUID (TArray (i,i) a, FreeSpace))
   , readNextSignal :: IO (Set (Signal i))
   , writeSuggestion :: Set (Signal i) -> IO () -- Bool DendritPatern 
   , suggestionPast :: TVar Free (HashMap (Set (Signal i))) ()
   , midleSignal :: TVar (SuggestionPath i)
   , suggestionError :: TVar Float
   --, midleSignalPast :: TVar Int
   -- , midleSignalPow2 :: TVar ([[Signal i]],[[Signal i]])
   , signalContext :: TVar (SuggestionPath i)
   -- , alwaysSensorReaction :: TVar (HashMap UUID (Set (i,i)))
   , maxSuggestion :: Int
   }

distanceSignal :: SuggestionPath i -> SuggestionPath i -> Int
distanceSignal ls1 ls2 = getSum $ fold $ zipWith (\s1 s2 -> if s1 == s2 then Sum 1 else Sum 0) ls1 ls2

filterSuggestionPast :: Int -> SuggestionPath i -> Free (HashMap (Set (Signal i))) () -> Free (HashMap (Set (Signal i))) ()
filterSuggestionPast dist ls hms = fst $ g ls hms (Sum 0)
   where
      g [] fhsm s = (fhsm,s)
      g ls (Free hmsn) s = fold fmap (\(k,hm)-> HMap.singletone k hm) $ fmap (\ (k,fhm) -> 
         let mlns = unsnoc ls
	 in fmap (\(ln,ns) -> if ns == k 
	    then let
	       (f,sU) = g ln fhm (s <> (Sum 1))
	       in if dist <= (getSum sU)
	          then (HMap.singletone k f, sU)
		  else (HMap.empty, sU)
	    else let
               (f,sU) = g ln fhm (s <> (Sum 0))
	       in if dist <= (getSum sU)
	          then (HMap.singletone k f, sU)
		  else (HMap.empty, sU)
	    ) mlns
	 ) $ toList hmsn 
      g _ (Pure ()) s = (Pure (), s)

lengthSuggestion :: Free (HashMap (Set (Signal i))) () -> Int -> Int
lengthSuggestion (Pure ()) s = s
lengthSuggestion (Free fhms) s = getMax $ fold $ map (\(_,fhm2)-> Max $ lengthSuggestion fhms (s+1) ) $ toList fhms

midleSuggestion' :: Free (HashMap (Set (Signal i))) () -> [SuggestionPath i]
midleSuggestion' (Pure ()) = [Seq.Empty]
midleSuggestion' (Free hm) = map (\ (k,fhm) -> fmap (k :) (midleSuggestion fhm) ) $ toList hm

type SuggestionOption i = [Set (Signal i)]

mapMSuggestion :: Monad m =>  
   (SuggestionPath i -> m (SugestionOption i)) -> SuggestionPath i -> Free (HashMap (Set (Signal i))) ()  -> m (Free (HashMap (Set (Signal i))) () )
mapMSuggestion f ck (Free hm) = fmap Free $ traverseWithKey  (\k fhm -> do
   fhmN <- mapMSuggestion f (ck :>| k) fhm
   return fhmN
   ) fhm 
mapMSuggestion f ck (Pure ()) = do
   so <- f ck
   return $ map (\k-> HMap.singletone (ck :>| k) (Pure ())) so

midleSuggestion :: Free (HashMap (Set (Signal i))) ()  -> SuggestionPath i
midleSuggestion f = fmap fst $ foldl (\ (ls,t) (k,Max ma2, Min mi2) -> 
         if t < (ma2 - mi2) then (ls,t) else (k, ma2 - mi2) ) ([[]], maxBound) $ 
      HMap.toList $ foldl (\hm hm2 -> unionWith <> hm hm2) HMap.empty $ do
         s1 <- ls
         s2 <- ls
         let dist = distanceSignal s1 s2
         guard $ not $ dist == (length s1)
         return ((HMap.singletine s1 (Max dist,Min dist)) <> (HMap.singletone s2 (Max dist, Min dist)) )
   where
      ls = midleSuggestion' f

type AdjDendritSCL i a = Env (DendritSC i a)

type AdjDendritSCR i a = Reader (DendritSC i a)

dendritSCIO :: 
   W.AdjointT 
      (AdjDendritSCL i a)
      (AdjDendritSCR i a)
      w
      b ->
   IO ()
dendritSCIO w = do
   let dsc = coask w 
   cSignal <- (readNextSignal dsc)
   fhm <- readTVarIO (fieldHM dsc)
   semiS <- readTVarIO (semiSense dsc)
   hmS <- readTVarIO (sensorHM dsc)
   hmU <- readTVarIO (reactionHM dsc)
   hmArr <- readTVarIO (fieldHM dsc)
   -- suggestionSafe
   sc <- readTVarIO (signalContext dsc)
   mids <- readTVarIO (midleSignal dsc)
   --(midSP1,midSP2) <- readTVarIO (midleSignalPow2 dsc) 
   suggP <- readTVarIO (suggestionPast dsc)
   let scn = cSignal : scn
   let distMiddle = distanceSignal scn mids
   --let distMiddleP1 = distanceSignal scn midSP1
   --let distMiddleP2 = distanceSignal scn midSP2
   let fSugg = filterSuggestionPast distMiddle scn suggP
   let lengthSCN = length scn  
   let midleN = midleSuggestion fSugg
   --midP <- readTVarIO (midleSignalPast dsc)
   se <- readTVarIO (suggestionError dsc)
   let be = (realToFrac distMidle) / (realToFrac lengthSCN) < se
   if ((\fs -> case fs of
         (Pure ()) -> True
	 (Free fm) -> (HMap.nil fm) || (lengthSuggestion midleN < (maxSuggestion dsc))
         ) fSugg) || be
      then do
         mapMSuggestion (\ kp -> do
            suggestionReSafeAll kp (unionWith <> hmS hmU) hmArr (lower w)
            when (Seq.nil kp) $ activationD cSignal hmArr
            --when (not $Seq.nil kp) $ activationD ((\(_ :>| k)->k) kp) hmArr
            dendritStepCycle' 
               (stepWave dsc) semiS (readActivedsc dsc) (queueActive dsc) hmS (liwer w) hmU hmArr
	    sactive <- readActive (readActiveDSC dsc) 
	    -- let distKP = distanceSignal 
	    let setD = foldl1 (\ (s1,Sum n1) (s2,Sum n2) -> if n1 > n2 then (s1,Sum n1) else (s2,Sum n2) ) $ HMap.toList sactive
	    ) (Seq.Empty) fSugg
      else do
         

 {-  where
      suggZero = do
         activationD cSignal freadActivehm
         dendritStepCycle' 
            (stepWave dsc) semiS (readActiveDSC dsc) (queueActive dsc) hmS (liwer w) hmU hmArr
-}        
   -- readActive
   


