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
   in if t < t2 then (t,kIn) else (t2,k2)

viewGeneral' :: (Eq a, Hashable a) => Seq a -> NextSeq a -> (Seq a, Seq a)
viewGeneral' sa ns = let
   km = HMap.keys $ generalPatternNS ns
   ks = HSet.toList $ uneqPattern ns
   (t,kIn) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else (x2,y2)) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, k) ) km
   ksIn = maybe [] id $ fmap HSet.toList $ (generalPatternNS ns) HMap.!? kIn
   -- ksAll = ks ++ ksIn
   (t2,k2) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else (x2,y2)) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, k) ) ks
   (t3,k3) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else (x2,y2)) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, k) ) ksIn
   in if t < t2 then (kIn,kIn) else if t2 < t3 then (kIn,k3) else (Seq.Empty,k2)


viewMinD x y = snd $ viewMinD' x y

viewTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Distance, Seq a)
viewTail sa ns = fmap (\s-> viewMinD' s ns) $ Seq.tails sa

viewTailWith :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, Distance, Seq a)
viewTailWith sa ns = fmap (\s-> (\(x,y)->(s,x,y)) $ viewMinD' s ns) $ Seq.tails sa

viewGeneralTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, Seq a)
viewGeneralTail sa ns = fmap (\s-> viewGeneral s ns) $ Seq.tails sa 

viewTailNoIn :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Distance, Seq a)
viewTailNoIn sa ns = fmap (\s-> (\(x,y)->(x, Seq.drop (Seq.length s) y) ) $ viewMinD' s ns) $ Seq.tails sa

type MaxContext = Int

type MaxError = Float 

type Hash = Int

data SuggestionHandler a = SuggestionHandler
   { inputA :: IO a
   , outputA :: a -> IO ()
   , suggestionView :: Seq a -> IO ()
   , currentContext :: TVar (Seq a)
   , currentNextSeq :: TVar (NextSeq a)
   , currentSuggestion :: TVar (Seq a)
   , currentFullSuggestion :: TVar (Seq a)
   , currentElementSuggestion :: TVar (Seq a)
   , maxContext :: MaxContext
   , maxError :: MaxError
   , shGeneralRadius :: GeneralRadius
   , shRadiusPattern :: RadiusPattern
   , shPowerSuggestion :: HashMap Hash (SuggestionHandler Hash)
   , shPSInput :: TVar Hash
   , shPSOutput :: TMVar Hash
   , shGeneralSuggestion :: Maybe (SuggestionHandler Hash)
   , shGSInput :: TVar Hash
   , shGSOutput :: TMVar Hash
   }
{-
type NotSuggestion gs bs m = LogicStateT gs bs m ()

class Suggstion gs bs a where
   lNextSeq :: Lens' gs (NextSeq a)
   lCurrentSuggestion :: Lens' bs (Seq a)
-}

addContext :: (MonadIO m, Eq a, Hashable a) => 
   SuggestionHandler a -> m a
addContext = do
   na <- liftIO $ inputA sh
   liftIO $ atomically $ modifyTVar (currentContext sh) (:|> na)
   liftIO $ atomically $ modifyTVar (currentContext sh) 
      (\s-> if Seq.length s > (maxContext sh) then f $ viewl s else s)
   return na 

zeroSuggestion :: (MonadIO m, Eq a, Hashable a) => 
   SuggestionHandler a -> m () -- LogicStateT gs bs m () -- (NotSuggestion gs bs m)
zeroSuggestion sh = do
   -- notS <- once $ backtrackWithRoll (\ _ _ -> return $ zeroBs sh) $ return () 
   na <- addContext
   -- (gs,bs) <- get
   ns <- liftIO $ readTVarIO (currentNextSeq sh)
   if not $ HMap.null $ generalPatternNS ns
      then do 
         ccn <- liftIO $ readTVarIO (currentContext sh)
         let (cs,_,_) = generalizationPattern (shGeneralRadius sh) $ Fold.foldl (HSet.union) HSet.empty $ fmap (HSet.singleton . snd) $ viewTailNoIn ccn ns
         let mnextA = cs Seq.!? 0 -- (Seq.length ccn)
         mapM (\nextA-> liftIO $ (outputA sh) nextA) mnextA
	 liftIO $ atomically $ writeTVar (currentSuggestion sh) cs 
	 return ()
      else return ()
   where
      f (_ Seq.:< s) = s
      f _ = Seq.Empty

stepSuggestion :: (MonadIO m, Eq a, Hashable a) => 
   SuggestionHandler a -> m () -- LogicStateT gs bs m () -- (NotSuggestion gs bs m)
stepSuggestion sh = do
   -- notS <- once $ backtrackWithRoll (\ _ _ -> return $ zeroBs sh) $ return () 
   na <- addContext
   -- (gs,bs) <- get
   ns <- liftIO $ readTVarIO (currentNextSeq sh)
   if not $ HMap.null $ generalPatternNS ns
      then do 
         csp <- liftIO $ readTVarIO (currentSuggestion sh)
	 cfsp <- liftIO $ readTVarIO (currentFullSuggestion sh)
	 cesp <- liftIO $ readTVarIO (currentElementSuggestion sh)
         ccn <- liftIO $ readTVarIO (currentContext sh)
         let mpastA = csp Seq.!? 0
	 mHashFS <- mapM (\ pastA -> do
	    if ns == pastaA
	       then do 
	          fmap join $ mapM (\shh-> do
	             let hashCFSP = hash cfsp
                     liftIO $ atomically $ writeTVar (shGSInput sh) hashCFSP
                     stepSuggestion shh
		     hashOut <- liftIO $ atomically $ readTMVar (shGSOutput sh)
                     let mlocalSH = (\x-> (shPowerSuggestion sh) HMap.!? x) =<< hashOut
		     mlH <- fmap join $ mapM (\lSH -> do
		        let hashCFSP = hash cesp
                        liftIO $ atomically $ writeTVar (shPSInput sh) hashCFSP
                        stepSuggestion lSH
		        hashOut <- liftIO $ atomically $ readTMVar (shPSOutput sh)
			return hashOut
		        ) mlocalSH
                     return $ (do 
		        x <- hashOut 
			return (x,mlH))
		  ) (shGeneralSuggestion sh)
	       else return Nothing
	    ) mpastA
	 let vtw = viewGeneralTail ccn ns
	 vtw2 <- maybe (return vtw) id (fmap (\ (hFS,mlh)
	       maybe (return vtw) id (fmap (\lh-> do
	          return $ Seq.filter (\(x,y) -> hash y == lh ) vtw
		  ) mlh)
	       ) mHahsFS
	    )
         -- let (cs,_,_) = generalizationPattern (shGeneralRadius sh) $ Fold.foldl (HSet.union) HSet.empty $ fmap (HSet.singleton . snd) $ viewTailNoIn ccn ns
         (cfs,ces) <- do
	    if Seq.length vtw2 == 1
	       then return $ vtw2 Seq.index 0
	       else do
                  let l = Seq.length vtw2
                  i <- liftIO $ randomRIO (0,l - 1)
		  return $ vtw2 Seq.index i
	 let mnextA = cs Seq.!? 0 -- (Seq.length ccn)
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
