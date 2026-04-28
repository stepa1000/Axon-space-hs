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
import Data.Logger

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

instance Logger (W.AdjointT
           (AdjArrayL (Int,Int) (BaseDendrit (Int,Int)))
           (AdjArrayR (Int,Int) (BaseDendrit (Int,Int)))
           (WAdjLogger Identity)) where
   logger = logger . lower
   loggerFile = loggerFile . lower

initializationADendritBD :: HasMapVarT (Int,Int) (BaseDendrit (Int, Int)) =>
   [String] ->
   FilePath ->
   IO ( AxonDendritSetting StdGen (BaseDendrit (Int,Int)) Int
      , W.AdjointT
           (AdjArrayL (Int,Int) (BaseDendrit (Int,Int)))
           (AdjArrayR (Int,Int) (BaseDendrit (Int,Int)))
           (WAdjLogger Identity)
           ())
initializationADendritBD tagLog fp = do
   print "initAxonDendritSetting pre"
   iads <- initAxonDendritSetting (0,0) (100,100) Proxy 11 11 (1,12) 1 (div 81 3) -- 27
   print "initAxonDendritSetting post"
   wLogger <- initWAdjLIO tagLog fp (Identity ())
   forkIO $ logUpdate wLogger
   w <- initializationADendrit iads (wLogger)
   return (iads,w)

mainPingPong :: IO ()
mainPingPong = do
   print "Init pre"
   (axdes,w) <- initializationADendritBD 
      ["pingDendrit"] "./log" -- initAxogenesPoint
   print "Init post"
   tvendDF <- newTVarIO False
   tvnowPic <- newTVarIO $ Pictures []
   --forkIO $ fDrow tvendDF tvnowPic w
   print "Fork pre"
   forkIO $ fPP tvendDF tvnowPic axdes w
   print "Fork post"
   animateIO 
      (InWindow "Dendrit PingPong" (1000,1000) (0,0))
      black
      (\_-> fDrow w )
      (\_-> return ())
   where
      fPP tvDF tvP axdes w = do
         pbf <- powerDendrit axdes w
         -- showGenerationDP axdes w -- pingPongDendrit axdes w
	 print "Post pingPongDendrit"
         atomically $ writeTVar tvDF True
	 print pbf
      fDrow w = adjCoDrowArrayNeiron w

mainDrowLines :: IO ()
mainDrowLines = do
   print "Init pre"
   (axdes,w) <- initializationADendritBD 
      ["updateIn2Box"] "./log" -- initAxogenesPoint
   print "Init post"
   tvendDF <- newTVarIO False
   tvnowPic <- newTVarIO $ Pictures []
   --forkIO $ fDrow tvendDF tvnowPic w
   animateIO 
      (InWindow "Dendrit lines" (1000,1000) (0,0))
      black
      (\_-> fDrow axdes )
      (\_-> return ())
   where
      fDrow axdes = do 
         let tl = listLine axdes
	 l <- readTVarIO tl
	 let ll = P.length l 
         i <- randomRIO (1,ll-1)
	 let (p1@(x1,y1),p2@(x2,y2)) = l !! i
	 i2 <- randomRIO (1,ll-1)
	 let li2 = l !! i2
	 i3 <- randomRIO (1,ll-1)
	 let li3 = l !! i3
	 return $ Pictures [dedritToPicture (p1,p2), dedritToPicture li2, dedritToPicture li3]

dedritToPicture (p1@(x1,y1),p2@(x2,y2)) = Color white $ Line [(realToFrac x1, realToFrac y1), (realToFrac x2, realToFrac y2)]
