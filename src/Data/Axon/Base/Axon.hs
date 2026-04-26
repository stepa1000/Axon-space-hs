{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.Axon where

import Prelude as P

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
import Control.Monad
import Control.Monad.Reader
import Control.Comonad.Trans.Adjoint as W
import Data.Array.MArray
import Debug.Trace
import Control.Lens
import System.Random
import Data.Map as Map
import Data.HashMap.Lazy as HMap
import Data.Set as Set
import Data.HashSet as HSet
import Control.Concurrent.Async
import Data.Traversable
import Data.Foldable as Fold
import Data.Proxy
import Data.UUID
import Data.Sequence as Seq
import Data.List as List
import Data.Monoid
import Data.Semigroup
import Control.Applicative
import Data.Maybe

import Data.Axon.Base.Types
import Data.Logger

-- Array

type AdjArrayL i a = Env (TArray i a)

type AdjArrayR i a = Reader (TArray i a)

-- | 
adjCoDrowLineV :: 
  ( Comonad w  
  , Ix x
  , Real x
  , Show x
  , Logger w
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
    ppi@(xpi@(x1,y1),ypi@(x2,y2)) <- getBounds (coask wa)
    when (x1 <= x && x <= x2 && y1 <= y0 + i && y0 + i <= y2) $ do
       logWSTM (lower wa) ["adjCoDrowLineV"] $ "adjCoDrowLineV:xy:" ++ (show (x,y0 + i))
       a0 <- readArray (coask wa) (x, y0 + i)
       writeArray (coask wa) (x, y0 + i) ((extract wa) a0)
       return ()
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
  , Logger w
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
    f y2 p2 (i+1)
  f _ _ _ = return ()
  f2 y p i = do
    ppi@(xpi@(x1,y1),ypi@(x2,y2)) <- getBounds (coask wa)
    when (x1 <= x0 + i && x0 + i <= x2 && y1 <= y && y <= y2) $ do
       logWSTM (lower wa) ["adjCoDrowLineH"] $ "adjCoDrowLineH:xy:" ++ (show (x0 + i,y))
       a0 <- readArray (coask wa) (x0+i, y)   
       writeArray (coask wa) (x0+i, y) ((extract wa) a0)
       return ()
    if p >= 0
      then do
        return (y+dir,p- 2*dx)
      else do
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
  , Logger w
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
adjCoDrowLine p0@(x0,y0) p1@(x1,y1) wa = do
  if abs (x1 - x0) > abs (y1 - y0)
    then adjCoDrowLineH p0 p1 wa
    else adjCoDrowLineV p0 p1 wa

adjCoDrowLineConst p0 p1 wa = adjCoDrowLine p0 p1 (fmap const wa) 

class HasMapVarT i a where
  mapVarTBool :: Lens' a (Map.Map i (TVar Bool, Set.Set i))

class HasNeiron a where
  neiron :: Lens' a (TVar Bool)

initNeiron :: 
  ( Ix i
  , HasMapVarT (i,i) a
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
    return ((set (mapVarTBool @(i,i) @_) Map.empty . set neiron tvN) a0)
    ) li
  -- print $ P.length li
  newListArray (p0,p1) la

type CxtAxon i w a g = 
  ( Comonad w
  , Ix i
  , Ix (i,i)
  , HasMapVarT (i,i) a
  , HasNeiron a
  , Random i
  , RandomGen g
  , Real i
  , Num i
  , Ord i
  , Show i
  -- , Show a
  , Integral i
  , CxtAxonNoG i w a
  )

type CxtAxonNoG i w a = 
  ( Comonad w
  , Ix i
  , Ix (i,i)
  , HasMapVarT (i,i) a
  , HasNeiron a
  , Random i
  -- , RandomGen g
  , Real i
  , Num i
  , Ord i
  , Show i
  -- , Show a
  , Integral i
  , Logger w
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
  logWSTM (lower w) ["lineAxon1"] $ "lineAxon1:pn:" ++ (show pn)
  an <- readArray arr pn
  let tvAxonN = an^.neiron
  logWSTM (lower w) ["lineAxon1"] $ "lineAxon1:p01:" ++ (show p0)
  logWSTM (lower w) ["lineAxon1"] $ "lineAxon1:p01:" ++ (show p1)
  adjCoDrowLine p0 p1 (fmap (const (\ a-> let
    mapTV = a^.mapVarTBool
    in set mapVarTBool (Map.insert pn (tvAxonN, Set.empty) mapTV) a
    )) w)

randomAxon :: 
  ( CxtAxon i w a g
  , Logger w
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
  logW (lower w) ["randomAxon", "getBounds"] $ "randomAxon:getBounds:" ++ (show ppi)
  logW (lower w) ["randomAxon","p0p1"] $ "randomAxon:p0:" ++ (show p0)
  logW (lower w) ["randomAxon","p0p1"] $ "randomAxon:p1:" ++ (show p1)
  if not $ p0 >= xpi && p1 <= ypi && p0 <= ypi && p1 >= xpi then error "randomAxon index bound error"
    else do
      rpi <- randomRIO (p0,p1)
      logW (lower w) ["randomAxon", "rpi"] $ "randomAxon:randomRIO:" ++ (show rpi)
      logW (lower w) ["randomAxon", "pn"] $ "randomAxon:pn:" ++ (show pn)
      atomically $ lineAxon1 pxy pn pn rpi w
      return rpi

randomAxoninBox ::
  ( CxtAxon i w a g
  , Logger w
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
  ppi@(xpi@(xi1,yi1),ypi@(xi2,yi2)) <- getBounds arr -- ???
  --let p0b = if p0 >= xpi && p0 <= ypi then p0 else xpi
  --let p1b = if p1 >= xpi && p1 <= ypi then p1 else ypi
  let x0b = fromJust $ fxp1 p0 ppi
  let y0b = fromJust $ fyp1 p0 ppi
  let x1b = fromJust $ fxp1 p1 ppi
  let y1b = fromJust $ fyp1 p1 ppi
  randomAxon pxy np (x0b,y0b) (x1b,y1b) w
  where
     fxp1 (x0,y0) (xpi@(xi1,yi1),ypi@(xi2,yi2)) = (do
        guard $ x0 < xi1
	return xi1
	) <|> (do
        guard $ x0 > xi2
	return xi2
	) <|> (do
	guard $ xi1 <= x0 && x0 <= xi2
        return x0
	)
     fyp1 (x0,y0) (xpi@(xi1,yi1),ypi@(xi2,yi2)) = (do
        guard $ y0 < yi1
	return yi1
	) <|> (do
        guard $ y0 > yi2
	return yi2
	) <|> (do
	guard $ yi1 <= y0 && y0 <= yi2
        return y0
	)

initAxonForNeironBox ::
  ( CxtAxon i w a g
  , Logger w
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
  logW (lower w) ["initAxonForNeironBox"] "Pre mapConcurrently"
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
      -- cha <- randomRSTM tvg (0,ca)
      -- if cha <= minca then return ()
      ae <- readArray arr p
      let mapA = ae^.(mapVarTBool @(i,i)) 
      let lk = Map.keys mapA
      let ll = P.length lk
      logWSTM (lower w) ["initAxogenesPoint"] $ "initAxogenesPoint:ll:" ++ (show ll)
      if ll <= 1 then return () 
         else do 
	 -- ril0 <- randomRSTM tvg (1,ll)
	 mapM_ (\ril0 -> do
            cha <- randomRSTM tvg (0,ca)
	    when (cha <= minca && ll > 1) $ do
	       ril1 <- randomRSTM tvg (1,ll - 1)
	       logWSTM (lower w) ["initAxogenesPoint"] $ "initAxogenesPoint:ril0:" ++ (show ril0)
	       logWSTM (lower w) ["initAxogenesPoint"] $ "initAxogenesPoint:ril1:" ++ (show ril1)
	       let kil1 = (lk !! ril1)
	       if ril0 == kil1 then return ()
	          else do
		  aen <- readArray arr p
		  writeArray arr p 
		     ( over 
		        (mapVarTBool @(i,i)) 
			( Map.adjust 
			     (\(tvb,seti)-> (tvb, Set.insert (lk !! ril1) seti) ) -- Maybe all order, nit ine side
			     (ril0) 
			. Map.adjust 
			     (\(tvb,seti)-> (tvb, Set.insert (ril0) seti) ) -- Maybe all order, nit ine side
			     (lk !! ril1)
			     ) 
			aen) 
            ) lk  

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
  return ()

updateAxogenesPoint ::
  ( CxtAxon i w a g
  ) =>
  Proxy g ->
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b -> 
  STM ()
updateAxogenesPoint pg (p :: (i,i)) w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then return () -- error "updateAxogenesPoint: index out of bounds"
    else do
      ae <- readArray arr p
      let mapA = ae^.(mapVarTBool @(i,i))
      logWSTM (lower w) ["updateAxogenesPoint"] $ "updateAxogenesPoint:size:mapA:" ++ (show $ Map.size mapA)
      _ <- Map.traverseWithKey (\ pk@(xk,yk) (tvbool, sp) -> do
         -- Map.Map i (TVar Bool, Set.Set i))
         logWSTM (lower w) ["updateAxogenesPoint"] $ "updateAxogenesPoint:size:sp:" ++ (show $ Set.size sp)
         boolAxon <- readTVar tvbool
         setBool <- foldlM (\ bn pset -> do -- pset
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
	    return $ bool2 : bn -- (snd mtvbool2sp2)
         -- return undefined
	    ) [] sp
	 -- let reBool = Fold.foldl (||) boolAxon setBool
	 -- writeTVar tvbool reBool
	 return ()
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
  Proxy g ->
  (i,i) ->
  W.AdjointT
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  STM ()
clearAxoginesPoint pg (p :: (i,i)) w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr
  if not $ p >= xpi && p <= ypi then return () -- $ error "updateAxogenesPoint: index out of bounds"
    else do
      ae <- readArray arr p
      let mapA = ae^.(mapVarTBool @(i,i))
      _ <- Map.traverseWithKey (\ pk@(xk,yk) (tvbool, sp) -> do
        writeTVar tvbool False
	) mapA
      return ()

updateIn2Box ::
  ( Comonad w-- CxtAxon i w a g
  , Logger w
  , Ix i
  , Integral i
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
  let r1 = round $ if r1' > r2' then r2' else r1'
  let r2 = round $ if r1' > r2' then r1' else r2'
  -- let intr2 = fromIntegral r2-- fromIntegral r2
  -- let intr1 = fromIntegral r1-- fromIntegral r1 -- r1 < r2
  -- logW (lower w) ["updateIn2Box"] $ "updateIn2Box:intr2:" ++ (show intr2)
  -- logW (lower w) ["updateIn2Box"] $ "updateIn2Box:intr1:" ++ (show intr1)  
  let (xb1,yb1) = xpi
  let (xb2,yb2) = ypi -- xpi < ypi ???????!!!!!!!!!!!!
  let (x0,y0) = p
  let rw = rangeSize (y0,yb2) -- w
  let rd = rangeSize (x0,xb2) -- d
  let rs = rangeSize (yb1,y0) -- s
  let ra = rangeSize (xb1,x0) -- a
  let lrw = range (y0,yb2) -- w
  let lrd = range (x0,xb2) -- d
  let lrs = range (yb1,y0) -- s
  let lra = range (xb1,x0) -- a
  let lww = range (min yb2 (y0 + r1), min yb2 (y0 + r2)) -- w
  let ldd = range (min (x0 + r1) xb2, min xb2 (x0 + r2)) -- d
  let lss = range (max yb1 (y0 - r2), max yb1 (y0 - r1)) -- s
  let laa = range (max xb1 (x0 - r2), max xb1 (x0 - r1)) -- a
  -- --------
  let lw = range (min yb2 y0, min yb2 (y0 + r1)) -- w
  let ld = range (min x0 xb2, min xb2 (x0 + r1)) -- d
  let ls = range (max yb1 (y0 - r1), max yb1 y0) -- s
  let la = range (max xb1 (x0 - r1), max xb1 x0) -- a
  let pwwd = liftA2 (,) lww ld
  let pwwdd = liftA2 (,) lww ldd
  let pwdd = liftA2 (,) lw ldd
  let psdd = liftA2 (,) ls ldd
  let pssdd = liftA2 (,) lss ldd -- ????????
  let pssd = liftA2 (,) lss ld
  let pssa = liftA2 (,) lss la
  let pssaa = liftA2 (,) lss laa
  let psaa = liftA2 (,) ls laa
  let pwaa = liftA2 (,) lw laa
  let pwwaa = liftA2 (,) lww laa
  let pwwa = liftA2 (,) lww la
  logW (lower w) ["updateIn2Box"] $ "updateIn2Box:pssaa:length:" ++ (show $ P.length pssaa)
  let in2BS = pwwd ++ pwwdd ++ pwdd ++ psdd ++ pssdd ++ pssd ++ pssa ++ pssaa ++ psaa ++ pwaa ++ pwwaa ++ pwwa
  forConcurrently_ in2BS (\i-> do
    atomically $ do
      f i w
    )

cube = Polygon [(0,0),(1,0),(1,1),(0,1),(0,0)] 

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
  writeArray arr p (Color red $ Polygon [(0,0),(1,0),(1,1),(0,1),(0,0)])

-- instance HasMapVarT 
{-
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
-}
drowWPic :: 
   W.AdjointT
      (AdjArrayL (Int,Int) Picture)
      (AdjArrayR (Int,Int) Picture)
      Identity
      () ->
   IO Picture
drowWPic w = do
  let arr = coask w
  ppi@(xpi,ypi) <- getBounds arr 
  lp <- mapM (\ p@(x,y) -> do
     pic <- readArray arr p 
     return $ Translate (fromIntegral x) (fromIntegral y) pic
     ) (range (xpi,ypi))
  return $ Pictures lp

updateIn2Radius :: 
  ( Comonad w-- CxtAxon i w a g
  , Logger w
  , Ix i
  , Num i
  , Integral i
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
  logW (lower w) ["updateIn2Radius"] $ "updateIn2Radius:r1:" ++ (show r1)
  logW (lower w) ["updateIn2Radius"] $ "updateIn2Radius:r2:" ++ (show r2)
  updateIn2Box (r1 / sqrt 2) (r2 * sqrt 2) p0
    (\ ip@(xi,yi) w -> do
      let rv = (xi - x0)^2 + (yi - y0)^2
      if (rv > (round r1)^2 ) && (rv < (round r2)^2 ) 
      then do
         f ip w
      else return ()
    ) 
    w

updateIn2RUpAxogenesPoint :: 
  ( Comonad w-- CxtAxon i w a g
  , Ix i
  , CxtAxon i w a g
  ) =>
  Proxy g ->
  Float -> -- ???? Int
  Float -> -- ????? Int
  (i,i) ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  IO ()
updateIn2RUpAxogenesPoint pg r1 r2 p0 w = 
   updateIn2Radius r1 r2 p0 (updateAxogenesPoint pg) w

updateIn2RUpClearAxoginesPoint ::  
  ( Comonad w-- CxtAxon i w a g
  , Ix i
  , CxtAxon i w a g
  ) =>
  Proxy g ->
  Float -> -- ???? Int
  Float -> -- ????? Int
  (i,i) ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  IO ()
updateIn2RUpClearAxoginesPoint pg r1 r2 p0 w = 
   updateIn2Radius r1 r2 p0 (clearAxoginesPoint pg) w

updateIn2RNeiron :: 
  ( Comonad w-- CxtAxon i w a g
  , Ix i
  , CxtAxon i w a g
  ) =>
  Proxy g ->
  Float -> -- ???? Int
  Float -> -- ????? Int
  (i,i) ->
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w
    b ->
  IO ()
updateIn2RNeiron pg r1 r2 p0 w =
   updateIn2Radius r1 r2 p0 (\ p wn -> do
      let arr = coask wn
      ae <- readArray arr p
      let tn = ae^.neiron
      writeTVar tn True
      ) w

waveInterval ::
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , Integral i 
   , Logger w
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
   ppi@(xpi@(x1,y1),ypi@(x2,y2)) <- getBounds arr 
   let arrR = sqrt ((fromIntegral $ x2 - x1) ^ 2 + (fromIntegral $ y2 - y1) ^ 2) 
   let l1 = [0,rA .. arrR]
   let l2 = [rA, rA * 2 .. arrR]
   logW (lower w) ["waveInterval"] $ "waveInterval:arrR:" ++ (show arrR )
   mapM (\(x,y) -> do 
      logW (lower w) ["waveInterval"] $ "waveInterval:" ++ (show (x,y))
      f x y p0 w) (P.zip l1 l2) 
   return ()

waveNeironTrue ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g
   ) => 
   Proxy g ->
   Float ->
   (i,i) ->
    W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
waveNeironTrue pg s i w = waveInterval s i (\ r1 r2 p wn -> updateIn2RNeiron pg r1 r2 p w) w

updateDedritSpace :: -- GOOD abstract the
  ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g
   ) => 
   Proxy g ->
   Float ->
   [(i,i)] ->
   ( W.AdjointT 
        (AdjArrayL (i,i) a)
        (AdjArrayR (i,i) a)
        w
        b ->
     IO c
    ) ->
    W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO c
updateDedritSpace pg s li f w = do
  forConcurrently_ li (\i-> do
    waveInterval s i (updateIn2RUpAxogenesPoint pg) w 
    )
  -- waveInterval s i updateIn2RUpAxogenesPoint w
  c <- f w
  waveInterval s (head li) (updateIn2RUpClearAxoginesPoint pg) w -- all array to false maybe ?????????!!!!!!!!!!!
  return c
   
upIn2RUpAxoginesPWave pg rA p0 w = waveInterval rA p0 (updateIn2RUpAxogenesPoint pg)

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
generateDendritPatern g p0@(px,py) r k w = do
   let arr = coask w
   ppi@(xpi,ypi) <- getBounds arr
   if not $ and [(px - r, py - r) >= xpi, (px + r, py + r) <= ypi] 
      then error "updateAxogenesPoint: index out of bounds" 
      else do
         let pxA = px - r
	 let pyA = py - r
	 let pxB = px + r
	 let pyB = py + r
	 fmap Fold.fold $ mapM (\i-> do
            p <- randomRSTM g ((pxA,pyA),(pxB,pyB))
            return $ Set.singleton p
	    ) [0,1 .. k ]

generateDendritPaternIO ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen StdGen
   , Random i
   , CxtAxon i w a StdGen
   ) => 
   (i,i) ->
   i ->
   Int -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (DendritPatern i)
generateDendritPaternIO p r k w = do
   std <- getStdGen
   tvstd <- newTVarIO std
   atomically $ generateDendritPatern tvstd p r k w
	
writeDendritPatern :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , Random i
   , CxtAxonNoG i w a
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
   mapM (\ i -> do
      a <- readArray arr i 
      let tvBool = a^.neiron
      writeTVar tvBool True  
      ) $ Set.toList dp
   return ()
   
readDendritPatern :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , Random i
   , CxtAxonNoG i w a
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
   ppi@(xpi@(x1,y1),ypi@(x2,y2)) <- getBounds arr
   let lx = range (x-r,x+r)
   let ly = range (y-r,y+r)
   foldlM (\ bn i@(xi,yi) -> 
      if x1 < xi && xi < x2 && y1 < yi && yi < y2
         then do
            a <- readArray arr i 
            let tvBool = a^.neiron
            b <- readTVar tvBool -- True
	    logWSTM (lower w) ["readDendritPatern"] $ "readDendritPatern:neiron:" ++ (show $ b)
	    if b then return $ Set.union bn (Set.singleton i)
	       else return $ bn
	 else return bn
      ) Set.empty (liftA2 (,) lx ly )

midleDP :: (Num i, Ord i, Integral i, Bounded i) => DendritPatern i -> (i,i)
midleDP dp | Set.null dp = (0,0)
midleDP dp = f $ Fold.fold $ fmap (\(x,y)-> (Max x,Min x, Max y, Min y)) $ Set.toList dp
   where
      f (Max maxX,Min minX,Max maxY,Min minY) = ((div (maxX - minX) (fromIntegral 2)) + minX ,(div (maxY - minY) (fromIntegral 2)) + minY )

updateDendritList :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   ) => 
   Proxy g ->
   WaveStep ->
   [PointAndR i] ->
   [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(DendritPatern i, PointAndR i)] -- (HashSet (DendritPatern i), PointAndR i)
updateDendritList pg ws lpr lldp w = do
   logW (lower w) ["updateDendritList"] "Start updateDendritList"
   ldpn <- mapM (\ldp -> do
      mapConcurrently (\dp-> atomically $ writeDendritPatern dp w) $ fmap fst ldp
      logW (lower w) ["updateDendritList"] "Post writeDendritPatern"
      updateDedritSpace pg ws (fmap snd ldp) (\ wn -> do
         mapConcurrently (\(p,r)-> do
            dpn <- atomically $ readDendritPatern p r w
	    logW (lower w) ["updateDendritList"] $ "updateDendritList:sizeDP:" ++ (show $ Set.size dpn)
	    logW (lower w) ["updateDendritList"] "Post readDendritPatern"
            return (dpn,(p,r))
	    ) lpr 
	 ) w
      ) lldp
   logW (lower w) ["updateDendritList"] "Start updateDendritList"
   return $ join ldpn -- ?????????

updateDendritListAnyDP :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Bounded i
   ) => 
   Proxy g ->
   WaveStep ->
   [PointAndR i] ->
   [[DendritPatern i]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(DendritPatern i, PointAndR i)] -- (HashSet (DendritPatern i), PointAndR i)
updateDendritListAnyDP pg ws lpr lldp w = do
   updateDendritList pg ws lpr ( (fmap . fmap) (\x-> (x, midleDP x)) lldp) w

class InitWM w m a where
   initWM :: w () -> m a

type InitWIODPMK1 g w i a = 
   ( InitWM w IO a
   , Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g 
   , HasMapVarT (i,i) a
   , Bounded i
   , Logger w
   )

data AxonDendritSetting g a i = AxonDendritSetting 
   { lowerIndex :: (i,i)
   , uperIndex :: (i,i)
   , proxyG :: Proxy g
   , lengthBox :: i
   , lengthPattern :: i
   , listLine :: TVar [(NeironPoint i,(i,i))]
   , adsChanceAxon :: ChanceAxon
   , adsWaveStep :: WaveStep
   , trayGeneration :: Int
   }

initAxonDendritSetting li ui pg lb lp aca ws tg = do
   tvl <- newTVarIO []
   return $ AxonDendritSetting li ui pg lb lp tvl aca ws tg

initNeironWIO :: InitWIODPMK1 g w i a => 
   AxonDendritSetting g a i -> 
   w () -> 
   IO ( W.AdjointT
           (AdjArrayL (i,i) a)
           (AdjArrayR (i,i) a)
           w
        ())
initNeironWIO axdes w = do
   a <- initWM w
   tarr <- initNeiron a (lowerIndex axdes) (uperIndex axdes) 
   return $ adjEnv tarr w

initAxonForNeironBoxWIO :: InitWIODPMK1 g w i a => 
   AxonDendritSetting g a i -> 
   W.AdjointT
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
initAxonForNeironBoxWIO axdes w = do
   lnpi <- initAxonForNeironBox (proxyG axdes) (lengthBox axdes) w
   atomically $ modifyTVar (listLine axdes) (lnpi ++)

allAxogenesPointWIO :: InitWIODPMK1 StdGen w i a => 
   AxonDendritSetting StdGen a i -> 
   W.AdjointT
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
allAxogenesPointWIO axdes w = do
   std <- initStdGen
   tvstd <- newTVarIO std
   allAxogenesPoint tvstd (adsChanceAxon axdes) w

initializationADendrit :: InitWIODPMK1 StdGen w i a => 
   AxonDendritSetting StdGen a i ->
   w () ->
   IO ( W.AdjointT
           (AdjArrayL (i,i) a)
           (AdjArrayR (i,i) a)
           w
           ())
initializationADendrit axdes w = do
   logW w ["initializationADendrit"] "Start initializationADendrit"
   adjArr <- initNeironWIO axdes w
   logW w ["initializationADendrit"] "Pre initAxonForNeironBoxWIO"
   initAxonForNeironBoxWIO axdes adjArr
   logW w ["initializationADendrit"] "Post initAxonForNeironBoxWIO"
   allAxogenesPointWIO  axdes adjArr
   logW w ["initializationADendrit"] "End initializationADendrit"
   return adjArr

updateADendrit :: InitWIODPMK1 StdGen w i a => 
   AxonDendritSetting StdGen a i -> 
   [PointAndR i] ->
   [[DendritPatern i]] ->
   W.AdjointT
           (AdjArrayL (i,i) a)
           (AdjArrayR (i,i) a)
           w
           () ->
   IO [(DendritPatern i, PointAndR i)]
updateADendrit axdes lpr ldp w = do
   updateDendritListAnyDP (Proxy @StdGen) (adsWaveStep axdes) lpr ldp w

distancePatern :: Ord i => DendritPatern i -> DendritPatern i -> Int
distancePatern dp1 dp2 = x
   where
      (Sum x) = foldMap (\p-> if Set.member p dp2 then Sum 1 else Sum 0) dp1

pingPongDendrit :: InitWIODPMK1 StdGen w i a => 
   AxonDendritSetting StdGen a i -> 
   W.AdjointT
           (AdjArrayL (i,i) a)
           (AdjArrayR (i,i) a)
           w
           () ->
   IO (Bool, Float)
pingPongDendrit axdes w = do
   let v = fromIntegral $ lengthPattern axdes
   let p1 = (\(x,y)->(x+v,y+v)) (lowerIndex axdes)
   let p2 = (\(x,y)->(x-v,y-v)) (uperIndex axdes)
   dp1 <- generateDendritPaternIO p1 (fromIntegral $ v) (trayGeneration axdes) w
   logW (lower w) ["pingPongDendrit"] "Post generateDendritPaternIO" -- size
   logW (lower w) ["pingPongDendrit"] $ "pingPongDendrit:sizeDP:" ++ (show $ Set.size dp1)
   [(dp2,_)]<- updateADendrit axdes [(p2,v)] [[dp1]] w
   logW (lower w) ["pingPongDendrit"] $ "pingPongDendrit:sizeDPOut:" ++ (show $ Set.size dp2)
   [(dp1N,_)]<- updateADendrit axdes [(p1,v)] [[dp2]] w
   return (dp1N == dp1, (realToFrac $ distancePatern dp1N dp1) / (realToFrac $ max (Set.size dp1N) (Set.size dp1)) )
   
showGenerationDP :: InitWIODPMK1 StdGen w i a => 
   AxonDendritSetting StdGen a i -> 
   W.AdjointT
           (AdjArrayL (i,i) a)
           (AdjArrayR (i,i) a)
           w
           () ->
   IO ()
showGenerationDP axdes w = do
   let v = fromIntegral $ lengthPattern axdes
   let p1 = (\(x,y)->(x+v,y+v)) (lowerIndex axdes)
   let p2 = (\(x,y)->(x-v,y-v)) (uperIndex axdes)
   dp1 <- generateDendritPaternIO p1 (fromIntegral $ v) (trayGeneration axdes) w
   atomically $ writeDendritPatern dp1 w

showWaveRDP :: InitWIODPMK1 StdGen w i a => 
   AxonDendritSetting StdGen a i -> 
   W.AdjointT
           (AdjArrayL (i,i) a)
           (AdjArrayR (i,i) a)
           w
           () ->
   IO ()
showWaveRDP axdes w = do
   let v = fromIntegral $ lengthPattern axdes
   let p1 = (\(x,y)->(x+v,y+v)) (lowerIndex axdes)
   let p2 = (\(x,y)->(x-v,y-v)) (uperIndex axdes)
   -- dp1 <- generateDendritPaternIO p1 (fromIntegral $ v) (trayGeneration axdes) w
   waveNeironTrue (proxyG axdes) 3 p1 w
   --updateIn2RNeiron (proxyG axdes) 9 12 p1 w
   --updateIn2RNeiron (proxyG axdes) 12 15 p1 w
   -- updateIn2RNeiron (proxyG axdes) 15 50 p1 w
   -- atomically $ writeDendritPatern dp1 w
   -- updateIn2RUpAxogenesPoint (proxyG axdes) 0 11 p1 w 
   -- updateIn2RUpAxogenesPoint (proxyG axdes) 0 22 p1 w

showAxogenesDP :: InitWIODPMK1 StdGen w i a => 
   AxonDendritSetting StdGen a i -> 
   W.AdjointT
           (AdjArrayL (i,i) a)
           (AdjArrayR (i,i) a)
           w
           () ->
   IO ()
showAxogenesDP axdes w = do
   let v = fromIntegral $ lengthPattern axdes
   let p1 = (\(x,y)->(x+v,y+v)) (lowerIndex axdes)
   let p2 = (\(x,y)->(x-v,y-v)) (uperIndex axdes)
   dp1 <- generateDendritPaternIO p1 (fromIntegral $ v) (trayGeneration axdes) w
   -- updateIn2RNeiron (proxyG axdes) 1 22 p1 w
   atomically $ writeDendritPatern dp1 w
   -- updateIn2RUpAxogenesPoint (proxyG axdes) 0 11 p1 w 
   updateIn2RUpAxogenesPoint (proxyG axdes) 11 12 p1 w




