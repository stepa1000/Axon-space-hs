{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Seq.Functional where

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
import Data.Maybe
-- import Control.Monad.LogicState

import Data.Axon.Base.Types
import Data.Seq.Base

data Fun a = Fun
   { funXY :: HashMap (Seq (Maybe a)) (Seq (Maybe a))
   }

randomFun :: Seq a -> IO (Fun a)
randomFun s = do
   let ls = Seq.length s
   i <- randomR (0,ls - 1)
   let (x,y) = Seq.splitAt i s
   let xl = Seq.length x
   let yl = Seq.langth y
   xi <- randomR (0,xl)
   yi <- randomR (0,yl)
   xn <- mapM (\a-> do
      xj <- randomR (0,xl)
      if xj < xi then return $ Just a
         else return Nothing
      ) x
   yn <- mapM (\a-> do
      yj <- randomR (0,yl)
      if yj < yi then return $ Just a
         else return Nothing
      ) y
   return $ Fun $ HMap.singleton xn yn
   

generationSuggestionFun :: Int -> Seq a -> IO [Fun a]
generationSuggestionFun i s = do
   mapM (\_-> do
      randomFun s
      ) [0,1 .. i]

unionFun' :: Fun a -> Fun a -> Maybe (Fun a)
unionFun' f1 f2 = if HMap.disjoint (funXY f1) (funXY f2) 
   then Just $ Fun $ HMap.union (funXY f1) (funXY f2)
   else Nothing

unionFun :: [Fun a] -> [Fun a]
unionFun [] = []
unionFun (x:l) = g $ Fold.foldl (\ (xf,l) f -> maybe (xf,f:l) (\fn-> (fn,l)) (unionFun' xf f) ) (x,[]) l
   where
      g (xf,l) = xf : (uninoFun l)

runFun :: Fun a -> Seq a -> Seq (Maybe a)
runFun f s = 
