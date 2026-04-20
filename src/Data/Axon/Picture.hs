{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Picture where

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
import Graphics.Gloss.Data.Color
import Graphics.Gloss.Data.Picture

import Data.Generics.Product.Fields

import Data.Axon.Base.Axon 

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
  , Real i
  , Ix i
  , CxtAxonNoG i w a 
  ) =>
  W.AdjointT 
    (AdjArrayL (i,i) a)
    (AdjArrayR (i,i) a)
    w 
    b ->
  IO Picture
adjCoDrowArrayNeiron w = do
  adjCoDrowArray (\a-> do
     bn <- readTVarIO $ a^.neiron
     return $ if bn
        then Color white $ cube
	else Pictures []) w
