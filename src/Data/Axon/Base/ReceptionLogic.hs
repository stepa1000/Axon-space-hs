{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.ReceptionLogic where

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
import Data.Hashable

import Data.Axon.Base.Types
import Data.Logger
import Data.Axon.Base.Axon 

generationRWSpace :: (Num im Ix i, Enum i) => AxonDendritSetting g a i -> [(i,i)]
generationRWSpace axdes = lp
   where
      li@(xl,yl) = lowerIndex axdes
      ui@(xu,yu) = uperIndex axdes
      v = lengthPattern axdes
      lx = [xl + v, xl + 2 * v .. xu]
      ly = [yl + v, yl + 2 * v .. yu]
      lp = liftA2 (,) lx ly

data ReceptionService r i = ReceptionService 
   { rsRWSpace :: TVar [(i,i)]
   , rsReception :: TVar (HasSet (i,i))
   , rsRection :: TVar (HashSet (i,i))
   , rsReceptionMapIn :: TVar (HashMap r (DendritPatern i))
   m rsReceptionMapOut :: TVar (HashMap (DendritPatern i) r)
   }
