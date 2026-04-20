{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module Visual where

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
import Data.Foldable
import Data.Proxy
import Data.UUID
import Data.Sequence as Seq
import GHC.Generics
import Control.Concurrent
import Graphics.Gloss.Interface.IO.Animate

import Data.Generics.Product.Fields

import Data.Axon.Base.Axon
import Data.Axon.Picture

-- main = mainPingPong 

data BaseDendrit i = BaseDendrit
   { intersectAD :: Map.Map i (TVar Bool, Set.Set i) -- HashMap ???????????
   , bdNeiron :: TVar Bool
   } deriving (Generic)

instance HasMapVarT i (BaseDendrit i) where
   mapVarTBool = field @"intersectAD"

instance HasNeiron (BaseDendrit i) where
   neiron = field @"bdNeiron"

initBaseDendrit = do
   tvb <- newTVarIO False
   return $ BaseDendrit Map.empty tvb

instance InitWM w IO (BaseDendrit i) where
   initWM _ = initBaseDendrit 

initializationADendritBD :: HasMapVarT (Int,Int) (BaseDendrit (Int, Int)) =>
   IO ( AxonDendritSetting StdGen (BaseDendrit (Int,Int)) Int
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
      (InWindow "Dendrit PingPong" (1000,1000) (0,0))
      black
      (\_-> fDrow w )
      (\_-> return ())
   where
      fPP tvDF tvP axdes w = do
         pbf <- pingPongDendrit axdes w
         atomically $ writeTVar tvDF True
	 print pbf
      fDrow w = adjCoDrowArrayNeiron w
