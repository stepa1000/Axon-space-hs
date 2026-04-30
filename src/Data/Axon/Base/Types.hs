{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.Types where

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
import Data.Monoid
import Data.Hashable

-- import Data.Axon.Base.Axon

type PointAndR i = ((i,i),i)

type WaveStep = Float 

distanceSeq :: Eq a => Seq a -> Seq a -> Float
distanceSeq slm1 slm2 = d / ml
   where
      ml = realToFrac $ max (Seq.length slm1) (Seq.length slm2) 
      d = getSum $ Fold.fold $ Seq.zipWith (\x y -> if x == y then Sum 1 else Sum 0) slm1 slm2

type GeneralRadius = Float

generalizationPattern :: (Eq a, Hashable a) =>
   GeneralRadius -> HashSet (Seq a) -> (Seq a,HashSet (Seq a), HashSet (Seq a))
generalizationPattern gr hsslm = (gslm,shsseqLM,zhsslm)
   where
      shsseqLM = HSet.filter (\slm-> (distanceSeq slm gslm) > gr ) hsslm
      zhsslm = HSet.filter (\slm-> not $ (distanceSeq slm gslm) > gr ) hsslm 
      (_,gslm) = Fold.foldl (\ (d1,slm1) (d2,slm2) -> if d1 > d2 then (d1,slm1) else (d2,slm2)) (0, Seq.Empty) ldslm
      ldslm = HSet.map (\slm1-> let
         ad = foldl1 (+) $ HSet.map (\slm2 -> distanceSeq slm1 slm2) hsslm
	 in (ad / (realToFrac $ HSet.size hsslm), slm1)) hsslm

