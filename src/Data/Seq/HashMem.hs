{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Seq.HashMem where

import Prelude as P

import GHC.Generics

import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM.TArray
import Control.Core.Composition
-- import Control.Base.Comonad
import Graphics.Gloss.Data.Picture
import Graphics.Gloss.Data.Color
import Data.Ix
import Data.Functor.Adjunction
import Control.Comonad
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env
import Control.Monad.Reader
import Control.Comonad.Trans.Adjoint as W
import Data.Array.MArray
import Debug.Trace
import Control.Lens
import Control.Monad
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
import Data.List
-- import Control.Monad.LogicState

import Data.Axon.Base.Types
import Data.Seq.Base

data HashInterval a = HashInterval 
   { hiCurrentSeq :: TVar (Seq a) 
   , hashInterval :: Int
   , hiIterator :: TVar Int
   --, hiSeq :: TVar (Seq Hash)
   }

initHashInterval :: Int -> TVar (Seq a) -> IO (HashInterval a)
initHashInterval i tvs = do
   tck <- newTVarIO 0
   --tvsh <- newTVarIO Seq.Empty
   return $ HashInterval tvs i tck

updateHI :: Hashable a => HashInterval a -> SuggestionHandlerSimple Hash -> IO (CoFreeStSug Hash Hash)
updateHI hi shs = do
  k <- readTVarIO $ hiIterator hi
  if k >= (hashInterval hi)
     then do
        atomically $ writeTVar (hiIterator hi) 0
        cs <- readTVarIO $ hiCurrentSeq hi
        let csh = hash cs
        initCoFreeStSug (hashInterval hi) (shs,csh)
     else do
        atomically $ modifyTVar (hiIterator hi) (+ 1)
        cs <- readTVarIO $ hiCurrentSeq hi
        let csh = hash cs
	initCoFreeStSugNL (hashInterval hi) (shs,csh)

upSuggestion :: (Hashable a, Show a) => Int -> SuggestionHandlerSimple a -> Hash -> a -> IO (Maybe (Seq a, StSuggestion a))
upSuggestion i shsa h a = do
   cfss <- initCoFreeStSug i (shsa,a)
   let lssa = seqSug i $ treeSug cfss
   let ss = (\(_ Cofree.:< (Comp1 wl) )-> coask wl ) cfss
   return $ getFirst $ Fold.fold $ fmap (\sa-> if hash sa == h then First $ Just (sa,ss) else First $ Nothing) lssa
   
data SuggestionPow a = SuggestionPow 
   { spSHSA :: SuggestionHandlerSimple a
   , spHI :: Maybe (HashInterval a)
   , spSP :: Maybe (SuggestionPow Hash)
   }

type PowSug = Int

initSuggestionPow :: (Hashable a, Show a) =>
   PowSug -> 
   Int ->
   MaxContext -> 
   MaxError ->
   GeneralRadius -> 
   RadiusPattern -> 
   IO (SuggestionPow a)
initSuggestionPow ps i mc me gr rp | ps <= 0 = do
   shs <- shsInit mc me gr rp
   return $ SuggestionPow shs Nothing Nothing
initSuggestionPow ps i mc me gr rp = do
   shs <- shsInit mc me gr rp
   hi <- initHashInterval i (shsCurrentContext shs)
   sp <- initSuggestionPow (ps - 1) i mc me gr rp
   return $ SuggestionPow shs (Just hi) (Just sp)

updateSuggestionPow :: (Hashable a, Show a) =>
   SuggestionPow a ->
   a ->
   IO (Maybe (Seq a))
updateSuggestionPow sp a = do
   let mhi = spHI sp
   let mshsh = spSP sp
   ms <- fmap join $ mapM (\(hi,shshm,sph) -> do
         cfss <- updateHI hi shshm
	 let lb = getSecondListCFSS cffss
	 mapM (\b-> do
            seqPreUSP <- readTVarIO $ hiCurrentSeq hi
	    msh <- updateSuggestionPow sph b
	    seqPostUSP <- readTVarIO $ hiCurrentSeq hi
	    ) lb
	          let mh = f msh
         fmap join $ mapM (\h -> do
	    msss <- upSuggestion (hashInterval hi) (spSHSA sp) h a
	    mapM (\(s,ss) -> do  
	       updateSTSuggestion ss (spSHSA sp)
	       return s
	       ) msss
	    ) mh
      ) $ join $ mhi >>= (\hi -> mshsh >>= (\shsh -> return $ return (hi,spSHSA shsh,shsh)))
   case ms of
      Nothing -> do 
         _ <- shsStepListNL (spSHSA sp) a
	 return Nothing
      (Just s) -> return (Just s)
   where
      f (Just (_ :<| (a :<| _))) = Just a
      f _ = Nothing
