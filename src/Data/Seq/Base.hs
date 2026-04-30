{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Seq.Base where

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

type RadiusPattern = Int

generationRadiusPattern :: (Eq a, Hashable a) =>
   RadiusPattern -> a -> Seq a -> HashSet (Seq a)
generationRadiusPattern rp a sa = let
   si = Seq.iterateN (Seq.length sa) (+ 1) 0
   sai = Seq.filter (\(x,y)->x == a) $ Seq.zip sa si
   in Fold.fold $ fmap (\(x,y)-> let 
     li = [y-rp, y-rp + 1 .. y + rp]
     in HSet.singleton $ Seq.fromList $ catMaybes $ fmap (\i-> sa Seq.!? i ) li
     ) sai

generationPatternBrackets :: (Eq a, Hashable a) =>
   a -> Seq a -> HashSet (Seq a)
generationPatternBrackets a sa = let
   si = Seq.iterateN (Seq.length sa) (+ 1) 0
   sai = Seq.filter (\(x,y)->x == a) $ Seq.zip sa si
   saif = f sai
   f (a1 :<| (a2 :<| s)) = (snd a1, snd a2) :<| (f $ a2 :<| s)
   f _ = Seq.Empty
   in Fold.fold $ fmap (\(x,y)-> let 
     li = [x, x + 1 .. y]
     in HSet.singleton $ Seq.fromList $ catMaybes $ fmap (\i-> sa Seq.!? i ) li
     ) saif

generationPattern :: (Eq a, Hashable a) =>
   RadiusPattern -> Seq a -> HashSet (Seq a)
generationPattern pr sa = Fold.foldl (HSet.union) (HSet.empty) $ fmap (\a-> let 
   p1 = generationRadiusPattern pr a sa
   p2 = generationPatternBrackets a sa
   in HSet.union p1 p2) sa

generalPattern :: Hashable a => GeneralRadius -> HashSet (Seq a) -> NextSeq a
generalPattern gr hs = let 
   (seq, seqIn ,seqOut ) = generalizationPattern gr hs
   ns = if not $ HSet.null seqIn then generalPattern gr seqOut
      else NextSeq (HMap.empty) ( seqOut)
   in ns {generalPatternNS = HMap.insert seq seqIn (generalPatternNS ns)}

data NextSeq a = NextSeq
   { generalPatternNS :: HashMap (Seq a) (HashSet (Seq a))
   , uneqPattern :: HashSet (Seq a)
   }

emptyNextSeq = NextSeq HMap.empty HSet.empty
{-
viewA :: a -> NextSeq a -> (HashMap (Seq a) (HashSet (Seq a)), HashSet (Seq a)) )
viewA a ns = undefined

viewSeqA :: Seq a -> NextSeq a -> (HashMap (Seq a) (HashSet (Seq a)), HashSet (Seq a))
viewSeqA a ns = undefined
-}

type Distance = Float

viewMinD' :: (Eq a, Hashable a) => Seq a -> NextSeq a -> (Distance, Seq a)
viewMinD' sa ns = let
   km = HMap.keys $ generalPatternNS ns
   ks = HSet.toList $ uneqPattern ns
   (t,kIn) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else (x2,y2)) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, k) ) km
   ksIn = maybe [] id $ fmap HSet.toList $ (generalPatternNS ns) HMap.!? kIn
   ksAll = ks ++ ksIn
   (t2,k2) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else (x2,y2)) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, k) ) ksAll
   in if t < t2 then kIn else k2

viewMinD x y = snd $ viewMinD' x y

viewTail :: Seq a -> NextSeq a -> Seq (Distance, Seq a)
viewTail sa ns = fmap (\s-> viewMinD' s ns) $ Seq.tails sa

type MaxContext = Int

type MaxError = Float 

data SuggestionHandler a = SuggestionHandler
   { inputA :: IO a
   , outputA :: a -> IO ()
   , suggestionView :: Seq a -> IO ()
   , currentContext :: TVar (Seq a)
   , currentNextSeq :: TVar (NextSeq a)
   , currentSuggestion :: TVar (Seq a)
   , maxContext :: MaxContext
   , maxError :: MaxError
   , shGeneralRadius :: GeneralRadius
   , shRadiusPattern :: RadiusPattern
   }
{-
type NotSuggestion gs bs m = LogicStateT gs bs m ()

class Suggstion gs bs a where
   lNextSeq :: Lens' gs (NextSeq a)
   lCurrentSuggestion :: Lens' bs (Seq a)
-}
zeroSuggestion :: (MonadIO m, Eq a, Hashable a) => 
   SuggestionHandler a -> m () -- LogicStateT gs bs m () -- (NotSuggestion gs bs m)
zeroSuggestion sh = do
   -- notS <- once $ backtrackWithRoll (\ _ _ -> return $ zeroBs sh) $ return () 
   na <- liftIO $ inputA sh
   liftIO $ atomically $ modifyTVar (currentContext sh) (:|> na)
   liftIO $ atomically $ modifyTVar (currentContext sh) 
      (\s-> if Seq.length s > (maxContext sh) then f $ viewl s else s)
   -- (gs,bs) <- get
   ns <- liftIO $ readTVarIO (currentNextSeq sh)
   if not $ HMap.null $ generalPatternNS ns
      then do 
         ccn <- liftIO $ readTVarIO (currentContext sh)
         let cs = viewMinD ccn ns
         let mnextA = cs Seq.!? (Seq.length ccn)
         mapM (\nextA-> liftIO $ (outputA sh) nextA) mnextA
	 liftIO $ atomically $ writeTVar (currentSuggestion sh) cs 
	 return ()
      else return ()
   where
      f (_ Seq.:< s) = s
      f _ = Seq.Empty

-- type LerningSuggestion gs bs m = LogicStateT gs bs m ()

lerningSuggestion :: (MonadIO m, Eq a, Hashable a) => 
   SuggestionHandler a -> m () -- (LerningSuggestion gs bs m)
lerningSuggestion sh = do
   -- lS <- once $ backtrack $ return () 
   ccn <- liftIO $ readTVarIO (currentContext sh)
   csn <- liftIO $ readTVarIO (currentSuggestion sh)
   if Seq.length ccn >= (maxContext sh) && distanceSeq ccn (Seq.take (maxContext sh) csn) < (maxError sh)
      then do
         let nns = generalPattern (shGeneralRadius sh) $ generationPattern (shRadiusPattern sh) ccn
         liftIO $ atomically $ modifyTVar (currentNextSeq sh) (\ns ->
	          ns { generalPatternNS = HMap.unionWith (HSet.union) (generalPatternNS ns) (generalPatternNS nns)
		      , uneqPattern = (HSet.union) (uneqPattern ns) (uneqPattern nns)
		      }
		  )
         return ()
      else do
	 return ()

updateZLSuggestion :: (MonadIO m, Eq a, Hashable a) => 
   SuggestionHandler a -> m ()
updateZLSuggestion sh = do
   zeroSuggestion sh
   csn <- liftIO $ readTVarIO (currentSuggestion sh)
   liftIO $ (suggestionView sh) csn
   lerningSuggestion sh
   updateZLSuggestion sh
