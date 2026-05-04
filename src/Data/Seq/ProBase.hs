{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Seq.ProBase where

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

import Data.Seq.Base
import Data.Axon.Base.Types

data FSuggestionHandler a = FSuggestionHandler
   { --pshfay1 :: (a -> y1)
    --, pshfxa :: (x1 -> a) -- it is not profunctor
     fInputA :: IO a
   , fOutputA :: a -> IO ()
   , fSuggestionView :: Seq a -> IO ()
   , fGenerationSuggestion :: (Seq a , Seq (Seq a, Seq a)) -> IO ()
   , fFilterSuggestion :: IO (Seq (Seq a, Seq a))
   , fCurrentContext :: TVar (Seq a)
   , fCurrentNextSeq :: TVar (NextSeq a)
   , fCurrentSuggestion :: TVar (Seq a)
   , fMaxContext :: MaxContext
   , fMaxError :: MaxError
   , fShGeneralRadius :: GeneralRadius
   , fShRadiusPattern :: RadiusPattern
   }

zeroFSuggestion :: (MonadIO m, Eq a, Hashable a) => 
   FSuggestionHandler a -> m () -- LogicStateT gs bs m () -- (NotSuggestion gs bs m)
zeroFSuggestion sh = do
   -- notS <- once $ backtrackWithRoll (\ _ _ -> return $ zeroBs sh) $ return () 
   na <- addContext
   -- (gs,bs) <- get
   ns <- liftIO $ readTVarIO (currentNextSeq sh)
   if not $ HMap.null $ generalPatternNS ns
      then do 
         ccn <- liftIO $ readTVarIO (currentContext sh)
	 let vtw = viewGeneralTail ccn ns
         (fGenerationSuggestion sh) (ccn, vtw)
	 vtw2 <- fFilterSuggestion sh
	 let l = Seq.length vtw2
         i <- liftIO $ randomRIO (0,l - 1)
	 (ccs,cce) <- vtw2 Seq.index i
         
         let mnextA = cs Seq.!? 0 -- (Seq.length ccn)
         mapM (\nextA-> liftIO $ (outputA sh) nextA) mnextA
	 liftIO $ atomically $ writeTVar (currentSuggestion sh) cs 
	 return ()
      else return ()
   where
      f (_ Seq.:< s) = s
      f _ = Seq.Empty

data ProSuggestionHandler a x y = ProSuggestionHandler
   { pshF1 :: x -> Seq a
   , pshF2 :: Seq a -> y
   , fsh :: FSuggestionHandler a
   }
