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

viewGeneral :: (Eq a, Hashable a) => Seq a -> NextSeq a -> (Seq a, Seq a)
viewGeneral sa ns = let
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

viewGeneralL :: (Eq a, Hashable a) => Seq a -> NextSeq a -> (Seq a, [Seq a])
viewGeneralL sa ns = let
   km = HMap.keys $ generalPatternNS ns
   ks = HSet.toList $ uneqPattern ns
   (t,kIn) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else (x2,y2)) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, k) ) km
   ksIn = maybe [] id $ fmap HSet.toList $ (generalPatternNS ns) HMap.!? kIn
   -- ksAll = ks ++ ksIn
   (t2,k2) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else 
         if x1 == x2 then (x1, y1 ++ y2) else (x2,y2) ) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, [k]) ) ks
   (t3,k3) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else 
         if x1 == x2 then (x1, y1 ++ y2) else (x2,y2) ) 
      (0,Seq.Empty) $ fmap (\k -> (distanceSeq sa k, [k]) ) ksIn
   in if t < t2 then (kIn,kIn) else if t2 < t3 then (kIn,k3) else (Seq.Empty,k2)

viewMinD x y = snd $ viewMinD' x y

viewTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Distance, Seq a)
viewTail sa ns = fmap (\s-> viewMinD' s ns) $ Seq.tails sa

viewTailWith :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, Distance, Seq a)
viewTailWith sa ns = fmap (\s-> (\(x,y)->(s,x,y)) $ viewMinD' s ns) $ Seq.tails sa

viewGeneralTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, Seq a)
viewGeneralTail sa ns = fmap (\s-> viewGeneral s ns) $ Seq.tails sa 

viewGeneralLTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, [Seq a])
viewGeneralLTail sa ns = fmap (\s-> viewGeneralL s ns) $ Seq.tails sa

data ViewSeqTail a = ViewSeqTail
   { -- context :: Seq a
     suggestion :: Seq a
   --, withappand :: Seq a
   , withoutappend :: Seq a
   }

viewGeneralLTailUp :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, [ViewSeqTail a])
viewGeneralLTailUp sa ns = let 
   sssa = viewGeneralLTail sa ns
   sta = Seq.tails sa 
   in fmap (\((cs,ls),s)-> f cs ls s ) $ Seq.zip sssa sta
   where 
      f cs ls s = fmap (\ss -> ViewSeqTail ss (Seq.drop (Seq.length s) ss)) ls

viewTailNoIn :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Distance, Seq a)
viewTailNoIn sa ns = fmap (\s-> (\(x,y)->(x, Seq.drop (Seq.length s) y) ) $ viewMinD' s ns) $ Seq.tails sa

type MaxContext = Int

type MaxError = Float 

type Hash = Int

data SuggestionHandlerSimple a = SuggestionHandlerSimple 
   { shsCurrentContext :: TVar (Seq a)
   , shsCurrentnextSeq :: TVar (NextSeq a)
   , shsCurrentSuggestion :: TVar (Seq (Seq a, [ViewSeqTail a]))
   , shsPowSuggestion :: Maybe (SuggestionHandlerSimple (Seq a))
   , shsMaxContext :: MaxContext
   , shsMaxError :: MaxError
   }

contextUp :: TVar (Seq a) -> MaxContext -> a -> IO ()
contextUp tvs mc na = do
   atomically $ modifyTVar tvs (:|> na)
   atomically $ modifyTVar tvs 
      (\s-> if Seq.length s > mc then f $ viewl s else s)
   return na 
   where
      f (_ Seq.:< s) = s
      f _ = Seq.Empty

-- Ben Azai looked and died.
-- Check past suggestion if not died, memrize that.
checkSuggestion :: TVar (Seq a) -> TVar (Seq (Seq a, [ViewSeqTail a])) -> IO (Seq a)
checkSuggestion tvs tvsugg = do
   cc <- readTVarIO tvs
   cs <- readTVarIO tvsugg
   if not $ Seq.null cc || Seq.null cs
      then do
         let lastA = cc Seq.!! ((Seq.length cc) - 1)
	 hss <- fmap (Fold.foldl HSet.union HSet.empty) $ mapM (\(sc,lvst) -> do
	    ls <- fmap catMaybes $ mapM (\ vst -> do
	       let was = withoutappend vst
	       if Seq.nill was then return Nothing
	          else do
		     let firstA = was Seq.!! 0
		     if lastA == firstA then return $ Just was
		        else return Nothing
	       ) lvst
	    let hss = Fold.foldl HSet.union HSet.empty $ fmap Seq.singleton ls
	    return hss
	    ) cs
	 let (midle, _, _) = generalizationPattern 0.2 hss
	 return midle
      else return Seq.Empty
-- checkView

updatePowSuggestion :: Maybe (SuggestionHandlerSimple (Seq a)) -> Seq a -> IO (Maybe (Seq a))
updatePowSuggestion mshs sa = do
   fmap join $ mapM (\shs-> do
      if Seq.null sa then return Nothing
         else do
	    shsStep shs sa
      ) mshs

lerningS :: (Eq a, Hashable a) => 
   TVar (Seq a) -> 
   TVar (NextSeq a) ->
   IO () -- (LerningSuggestion gs bs m)
lerningS tcc tns = do
   -- lS <- once $ backtrack $ return () 
   ccn <- liftIO $ readTVarIO tcc
   let nns = generalPattern (shGeneralRadius sh) $ generationPattern (shRadiusPattern sh) ccn
   atomically $ modifyTVar tns (\ns ->
          ns { generalPatternNS = HMap.unionWith (HSet.union) (generalPatternNS ns) (generalPatternNS nns)
	      , uneqPattern = (HSet.union) (uneqPattern ns) (uneqPattern nns)
	      }
	  )

checkView :: 
   Seq a -> 
   (Maybe (Seq a)) -> 
   TVar (Seq a) -> 
   TVar (Seq (Seq a, [ViewSeqTail a])) ->
   TVar (NextSeq a) ->
   IO (Maybe a)
checkView ts mS tvc tvs tns = do
   cc <- readTVarIO tvc
   cs <- readTVarIO tvs 
   -- ns <- readTVarIO tns
   let nssvst = viewGeneralLTailUp cc ns
   if (Seq.null ts || Seq.null nssvst)  
      then do
         lerningS tvc tns
         let nssvst2 = viewGeneralLTailUp cc ns
         atomically $ writeTVar tvs nssvst2
      else do
         s <- maybe 
	    ( do
	       let hss = Fold.foldl HSet.union HSet.empty $ fmap (Fold.foldl HSet.union HSet.empty . fmap (HSet.singleton . withoutappend) . snd) nssvst
               let (midle, _, _) = generalizationPattern 0.2 hss
	       return midle
	    ) 
	    return mS
         atomically $ writeTVar tvs nssvst 
	 if Seq.null s then return Nothing
	    else return $ Just # s Seq.!! 0

{-
Бен Азай взглянул и умер. 
Бен Зома взглянул и повредился [в уме]. 
Элиша бен Абуя стал «вырывать саженцы» (Маймонид видит в этом желание постичь нечто большее, чем возможно для человеческого разумения). 
Рабби Акива «вошёл с миром и вышел с миром».

Ben Azai looked and died.
Ben Zoma looked and was damaged [in his mind].
Elisha ben Abuya began to “pluck up seedlings” (Maimonides sees in this a desire to comprehend something greater than is possible for human understanding).
Rabbi Akiva "entered in peace and left in peace."
-}

shsStep :: (Eq a, Hashable a) => 
   SuggestionHandlerSimple a
   a -> 
   IO (Maybe a)
shsStep shs a = do
   -- Ben Azai looked and died.
   contextUp (shsCurrentContext shs) (shsMaxContext shs) a
   -- Ben Zoma looked and was damaged [in his mind].
   cs <- checkSuggestion (shsCurrentContext shs) (shsCurrentSuggestion shs)
   -- Elisha ben Abuya began to “pluck up seedlings” (Maimonides sees in this a desire to comprehend something greater than is possible for human understanding).
   mncs <- updatePowSuggestion (shsPowSuggestion shs) cs
   checkView cs mncs (shsCurrentContext shs) (shsCurrentSuggestion shs) (shsCurrentnextSeq shs)
   -- Rabbi Akiva "entered in peace and left in peace."

data SuggestionHandler a = SuggestionHandler
   { inputA :: IO a
   , outputA :: a -> IO ()
   , suggestionView :: Seq a -> IO ()
   , currentContext :: TVar (Seq a)
   , currentNextSeq :: TVar (NextSeq a)
   , currentSuggestion :: TVar (Seq a)
   --, currentFullSuggestion :: TVar (Seq a)
   --, currentElementSuggestion :: TVar (Seq a)
   , maxContext :: MaxContext
   , maxError :: MaxError
   , shGeneralRadius :: GeneralRadius
   , shRadiusPattern :: RadiusPattern
   {-, shPowerSuggestion :: HashMap Hash (SuggestionHandler Hash)
   , shPSInput :: TVar Hash
   , shPSOutput :: TMVar Hash
   , shGeneralSuggestion :: Maybe (SuggestionHandler Hash)
   , shGSInput :: TVar Hash
   , shGSOutput :: TMVar Hash-}
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
   where
      f (_ Seq.:< s) = s
      f _ = Seq.Empty

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
{-
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
	 -- rigth now i need do thet buuuut .... 
	 let mnextA = cs Seq.!? 0 -- (Seq.length ccn)
         mapM (\nextA-> liftIO $ (outputA sh) nextA) mnextA
	 liftIO $ atomically $ writeTVar (currentSuggestion sh) cs 
	 return ()
      else return ()
   where
      f (_ Seq.:< s) = s
      f _ = Seq.Empty
-}

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
