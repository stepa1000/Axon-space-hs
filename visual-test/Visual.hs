{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Wisual where

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

import Data.Generics.Product.Fields

import Data.Axon.Base.Axon

main = mainPingPong 

cube :: Picture
cube = Polygon [(0,0),(1,0),(1,1),(0,1),(0,0)]

adjCoDrowArray :: 
  ( Comonad w
  , Real x
  , Ix x
  ) =>
  (a -> IO Picture) ->
  W.AdjointT 
    (AdjArrayL (x,x) a)
    (AdjArrayR (x,x) a)
    w 
    b ->
  IO Picture
adjCoDrowArray f w = do
  lip <- getAssocs (coask w)
  lp <- mapM (\((x,y),a)-> fmap (Translate (realToFrac x) (realToFrac y)) $ f a ) lip
  return $ Pictures lp
 
adjCoDrowArrayNeiron ::  
  ( Comonad w
  , Real x
  , Ix x
  , CxtAxon i w a g 
  ) =>
  W.AdjointT 
    (AdjArrayL (x,x) a)
    (AdjArrayR (x,x) a)
    w 
    b ->
  IO Picture
adjCoDrowArrayNeiron w = do
  adjCoDrowArray (\a-> do
     readTVarIO $ a^.neiron
     return $ if 
        then return $ Color white $ cube
	else return $ Pictures []) w

data BaseDendrit i = BaseDendrit
   { intersectAD :: Map.Map i (TVar Bool, Set.Set i) -- HashMap ???????????
   , bdNeiron :: TVar Bool
   }

instance HasMapVarT i a where
   mapVarTBool = field @"intersectAD"

instance HasNeiron a where
   neiron = field @"bdNeiron"

initBaseDendrit = do
   tvb <- newTVarIO False
   return $ BaseDendrit Map.empty tvb

instacne InitWM w IO (BaseDendrit i) where
   initWM _ = initBaseDendrit 

initializationADendritBD :: 
   IO ( AxonDendritSetting (BaseDendrit (Int,Int)) Int
      , W.AdjointT
           (AdjArrayL (Int,Int) (BaseDendrit (Int,Int)))
           (AdjArrayR (Int,Int) (BaseDendrit (Int,Int)))
           Identity
           ())
initializationADendritBD = do
   iads <- initAxonDendritSetting (0,0) (1000,1000) Proxy 11 3 (1,3) 6 (div 81 3) -- 27
   w <- initializationADendrit iads (Identity ())
   return (iads,w)

mainPingPong :: IO ()
mainPingPong = do
   (axdes,w) <- initializationADendritBD 
   tvendDF <- newTVarIO False
   tvnowPic <- newTVarIO $ Pictures []
   --forkIO $ fDrow tvendDF tvnowPic w
   forkIO $ fPP tvendDF tvnowPic axdes w
   animateIO 
      (InWindow "Dendrit PingPong" black)
      (\_-> fDrow w )
      (\_-> return ())
   where
      fPP tvDF tvP axdes w = do
         pbf <- pingPongDendrit axdes w
         atomicaly $ writeTVar tvDF True
	 print pdf
      fDrow w = adjCoDrowArrayNeiron w
