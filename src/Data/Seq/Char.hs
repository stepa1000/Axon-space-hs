{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Seq.Char where

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
-- import Control.Monad.LogicState

import Data.Axon.Base.Types
import Data.Seq.Base

initSuggestionHandlerChar :: 
   MaxContext -> 
   MaxError -> 
   GeneralRadius -> 
   RadiusPattern -> 
   IO (SuggestionHandler Char)
initSuggestionHandlerChar mc me gr rp = do
   tstr <- newTVarIO ""
   tcc <- newTVarIO Seq.Empty
   tcns <- newTVarIO emptyNextSeq
   tcs <- newTVarIO Seq.Empty
   return $ SuggestionHandler
      (do
         str <- readTVarIO tstr
         f str tstr
	 )
      (\c-> do
         str <- readTVarIO tstr
         g str c
      )
      (\ seqC -> do
         print $ "Current suggestion:" ++ (show seqC)
	 )
      tcc
      tcns
      tcs
      mc
      me
      gr
      rp
   where
      g (c:str) c2 = do
         print $ "Eq char:" ++ (show $ c == c2) ++ ":C1:" ++ (show c) ++ ":C2:" ++ (show c2) ++ "\n"
      g _ c = do
         putStrLn "Null string"
      f :: String -> TVar String -> IO Char
      f (c:str) tstr = do
         atomically $ writeTVar tstr str
         return c
      f _ tstr = do
         putStrLn "Write string line:"
         str <- getLine
	 f str tstr

