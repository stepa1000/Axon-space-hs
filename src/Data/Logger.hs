{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Logger where

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
import Data.Foldable as Fold
import Data.Proxy
import Data.UUID
import Data.Sequence as Seq

import Data.Generics.Product.Fields

-- import Data.Axon.Base.Axon
-- import Data.Axon.Picture

class Comonad w => Logger w where
   logger :: w b -> HashSet String
   loggerFile :: w b -> FilePath
   loggerQueue :: w b -> TQueue String

logW :: Logger w => w b -> [String] -> String -> IO ()
logW w tags str = do
   let hstags = logger w
   let fp = loggerFile w
   if and $ fmap (\t-> HSet.member t hstags) tags
      then writeFile fp str
      else if HSet.member "logFalse" hstags 
         then writeFile fp $ "logFalse for tags: " ++ (show tags)
	 else return ()

data DataLogger = DataLogger
   { tagsLogger :: HashSet String
   , fileLogger :: FilePath 
   , queueLogger :: TQueue String
   }

type AdjLoggerL = Env DataLogger

type AdjLoggerR = Reader DataLogger

type WAdjLogger w = W.AdjointT
    AdjLoggerL
    AdjLoggerR
    w

initWAdjL :: Comonad w => [String] -> FilePath -> w () -> WAdjLogger w () 
initWAdjL ls fp w = initWAdjLogger (DataLogger (Fold.fold $ fmap (HSet.singleton) ls) fp) w

initWAdjLogger :: Comonad w => DataLogger -> w () -> WAdjLogger w ()
initWAdjLogger dl w = adjEnv dl w

instance Comonad w => Logger (WAdjLogger w) where
   logger w = tagsLogger $ coask w 
   loggerFile w = fileLogger $ coask w 

