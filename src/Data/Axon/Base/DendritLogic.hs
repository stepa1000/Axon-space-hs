{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.DendritLogic where

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
import Control.Monad.Logic

import Data.Axon.Base.Axon
import Data.Axon.Base.Types

updateDendritLogic :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   ) => 
   WaveStep ->
   [PointAndR i] ->
   [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (DendritPatern i, PointAndR i) -- (HashSet (DendritPatern i), PointAndR i)
updateDendritLogic ws lpr ldp w = do
   lift $ mapConcurrently (\dp-> atomicaly $ writeDendritPatern dp w) $ fmap fst ldp
   ldp <- lift $ updateDedritSpace ws (fmap snd ldp) $ \ wn -> do
      mapM (\lpr -> do
         mapConcurrently (\(p,r)-> do
            dpn <- atomicaly $ readDendritPatern p r
            return (HSet.singletone dpn,(p,r))
	    ) lpr 
         ) llpr
   f $ fmap (return . join) ldp
   where
      f (x:xs) = x `interleave` (f xs)
      f (x:[]) = x
      f [] = empty

class Memorize i a where
   lPattern :: Lens' a (Seq (HashSet (DendritPatern i)))
   lPatternMax :: Lens' a Int
   lLenghtPattern :: Lens' a Int

dlMemorizeRight ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   (DendritPatern i, PointAndR i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (Either (PointAndR i) (PointAndR i)) -- LogicT IO (Either (PointAndR i) (PointAndR i))
dlMemorizeRight dppr w = do
   
    
   

