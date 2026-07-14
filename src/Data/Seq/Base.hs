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
-- import Control.Base.Comonad
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
      (0,[]) $ fmap (\k -> (distanceSeq sa k, [k]) ) ks
   (t3,k3) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else 
         if x1 == x2 then (x1, y1 ++ y2) else (x2,y2) ) 
      (0,[]) $ fmap (\k -> (distanceSeq sa k, [k]) ) ksIn
   in if t < t2 then (kIn,[kIn]) else if t2 < t3 then (kIn,k3) else (Seq.Empty,k2)

viewMinD x y = snd $ viewMinD' x y

viewTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Distance, Seq a)
viewTail sa ns = fmap (\s-> viewMinD' s ns) $ Seq.tails sa

viewTailWith :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, Distance, Seq a)
viewTailWith sa ns = fmap (\s-> (\(x,y)->(s,x,y)) $ viewMinD' s ns) $ Seq.tails sa

viewGeneralTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, Seq a)
viewGeneralTail sa ns = fmap (\s-> viewGeneral s ns) $ Seq.tails sa 

viewGeneralLTail :: (Eq a, Hashable a) => Seq a -> NextSeq a -> Seq (Seq a, [Seq a])
viewGeneralLTail sa ns = fmap (\s-> viewGeneralL s ns) $ Seq.tails sa

{-
viewGeneralLOR :: (Eq a, Hashable a) => Seq [a] -> NextSeq [a] -> (Seq [a], [Seq [a]])
viewGeneralLOR sa ns = let
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
      (0,[]) $ fmap (\k -> (distanceSeq sa k, [k]) ) ks
   (t3,k3) = Fold.foldl 
      (\ (x1,y1) (x2,y2) -> if x1 > x2 then (x1,y1) else 
         if x1 == x2 then (x1, y1 ++ y2) else (x2,y2) ) 
      (0,[]) $ fmap (\k -> (distanceSeq sa k, [k]) ) ksIn
   in if t < t2 then (kIn,[kIn]) else if t2 < t3 then (kIn,k3) else (Seq.Empty,k2)
-}

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
   in fmap (\((cs,ls),s)-> (cs, f cs ls s )) $ Seq.zip sssa sta
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
   , shsRadiusPattern :: RadiusPattern
   , shsGeneralRadius :: GeneralRadius
   }

contextUp ::  (Eq a, Hashable a) => TVar (Seq a) -> MaxContext -> a -> IO ()
contextUp tvs mc na = do
   atomically $ modifyTVar tvs (:|> na)
   atomically $ modifyTVar tvs 
      (\s-> if Seq.length s > mc then f $ viewl s else s)
   return ()
   where
      f (_ Seq.:< s) = s
      f _ = Seq.Empty

-- Ben Azai looked and died.
-- Check past suggestion if not died, memrize that.
checkSuggestion :: (Eq a, Hashable a, Show a) => TVar (Seq a) -> TVar (Seq (Seq a, [ViewSeqTail a])) -> IO (Seq a)
checkSuggestion tvs tvsugg = do
   cc <- readTVarIO tvs
   cs <- readTVarIO tvsugg
   if not $ Seq.null cc && Seq.null cs
      then do
         let lastA = fromJust $ cc Seq.!? ((Seq.length cc) - 1)
	 hss <- fmap (Fold.foldl HSet.union HSet.empty) $ mapM (\(sc,lvst) -> do
	    ls <- fmap catMaybes $ mapM (\ vst -> do
	       let was = withoutappend vst
               putStrLn $ "Full:Suggestion: " ++ (show $ suggestion vst)
	       putStrLn $ "Suggestion: " ++ (show was)
	       if Seq.null was then return Nothing
	          else do
		     let firstA = fromJust $ was Seq.!? 0
		     if lastA == firstA then return $ Just was
		        else return Nothing
	       ) lvst
	    let hss = Fold.foldl HSet.union HSet.empty $ fmap HSet.singleton ls
	    return hss
	    ) cs
	 let (midle, _, _) = generalizationPattern 0.2 hss
         putStrLn $ "Length midle: " ++ (show $ Seq.length midle)
         putStrLn $ "Length HashSet: " ++ (show $ HSet.size hss)
	 if Seq.null midle
	    then if HSet.null hss
	       then return Seq.empty
	       else return $ head $ HSet.toList hss
	    else return midle
      else return Seq.Empty
-- checkView

checkSuggestionList :: (Eq a, Hashable a, Show a) => TVar (Seq a) -> TVar (Seq (Seq a, [ViewSeqTail a])) -> IO [Seq a]
checkSuggestionList tvs tvsugg = do
   cc <- readTVarIO tvs
   cs <- readTVarIO tvsugg
   if not $ Seq.null cc && Seq.null cs
      then do
         let lastA = fromJust $ cc Seq.!? ((Seq.length cc) - 1)
	 hss <- fmap (Fold.foldl HSet.union HSet.empty) $ mapM (\(sc,lvst) -> do
	    ls <- fmap catMaybes $ mapM (\ vst -> do
	       let was = withoutappend vst
               putStrLn $ "Full:Suggestion: " ++ (show $ suggestion vst)
	       putStrLn $ "Suggestion: " ++ (show was)
	       if Seq.null was then return Nothing
	          else do
		     let firstA = fromJust $ was Seq.!? 0
		     if lastA == firstA then return $ Just was
		        else return Nothing
	       ) lvst
	    let hss = Fold.foldl HSet.union HSet.empty $ fmap HSet.singleton ls
	    return hss
	    ) cs
	 let (midle, _, _) = generalizationPattern 0.2 hss
         putStrLn $ "Length midle: " ++ (show $ Seq.length midle)
         putStrLn $ "Length HashSet: " ++ (show $ HSet.size hss)
	 return $ HSet.toList hss
      else return Seq.Empty

updatePowSuggestion ::  (Eq a, Hashable a, Show a) => Maybe (SuggestionHandlerSimple (Seq a)) -> Seq a -> IO (Maybe (Seq a))
updatePowSuggestion mshs sa = do
   fmap join $ mapM (\shs-> do
      if Seq.null sa then return Nothing
         else do
	    shsStep shs sa
      ) mshs

updatePowSuggestionList ::  (Eq a, Hashable a, Show a) => Maybe (SuggestionHandlerSimple (Seq a)) -> Seq a -> IO [Seq a]
updatePowSuggestionList mshs sa = do
   fmap join $ mapM (\shs-> do
      if Seq.null sa then return Nothing
         else do
	    shsStepList shs sa
      ) mshs

lerningS :: (Eq a, Hashable a) => 
   SuggestionHandlerSimple a ->
   TVar (Seq a) -> 
   TVar (NextSeq a) ->
   IO () -- (LerningSuggestion gs bs m)
lerningS sh tcc tns = do
   -- lS <- once $ backtrack $ return () 
   ccn <- liftIO $ readTVarIO tcc
   let nns = generalPattern (shsGeneralRadius sh) $ generationPattern (shsRadiusPattern sh) ccn
   atomically $ modifyTVar tns (\ns ->
          ns { generalPatternNS = HMap.unionWith (HSet.union) (generalPatternNS ns) (generalPatternNS nns)
	      , uneqPattern = (HSet.union) (uneqPattern ns) (uneqPattern nns)
	      }
	  )

checkView :: (Eq a, Hashable a) =>
   SuggestionHandlerSimple a ->
   Seq a -> 
   (Maybe (Seq a)) -> 
   TVar (Seq a) -> 
   TVar (Seq (Seq a, [ViewSeqTail a])) ->
   TVar (NextSeq a) ->
   IO (Maybe a)
checkView sh ts mS tvc tvs tns = do
   cc <- readTVarIO tvc
   cs <- readTVarIO tvs 
   ns <- readTVarIO tns
   let nssvst = viewGeneralLTailUp cc ns
   -- putStrLn $ "Length suggestion: " ++ (Seq.length nssvst)
   if Seq.null ts -- && (and $ Fold.fold $ fmap ((:[]) . and . fmap (Seq.null . withoutappend) . snd) nssvst)
      then do
         lerningS sh tvc tns
         let nssvst2 = viewGeneralLTailUp cc ns
         atomically $ writeTVar tvs nssvst2
	 putStrLn "Lern"
	 return Nothing
      else do
         -- let nssvst = fmap (\(x,y) fmap (\) y) nssvst'
         s <- maybe 
	    ( do
	       --let hss = Fold.foldl HSet.union HSet.empty $ fmap (Fold.foldl HSet.union HSet.empty . fmap (HSet.singleton . withoutappend) . snd) nssvst
	       let hswa = Fold.foldl HMap.union HMap.empty $ fmap (Fold.foldl HMap.union HMap.empty . fmap (\x-> HMap.singleton (suggestion x) (withoutappend x) ) . snd) nssvst
	       let hss = Fold.foldl HSet.union HSet.empty $ fmap (Fold.foldl HSet.union HSet.empty . fmap (HSet.singleton . suggestion) . snd) nssvst
               let (midle, _, _) = generalizationPattern 0.2 hss
	       let sn = maybe Seq.empty id $ hswa HMap.!? midle
	       if Seq.null sn then return $ f nssvst 0 0
	          else return sn
	    ) 
	    return $ join $ fmap (\s-> if Seq.null s then Nothing else Just s) mS
         atomically $ writeTVar tvs nssvst 
	 if Seq.null s then return $ ts Seq.!? 0 --Nothing
	    else return $ s Seq.!? 0
   where
      f nssvst i j 
         | Seq.length nssvst <= i = Seq.empty
	 | P.length (snd $ Seq.index nssvst i) <= j = f nssvst (i + 1) 0
      f nssvst i j = if Seq.null sn then f nssvst i (j+1) else sn
         where
	    sn = (withoutappend $ (\l-> l P.!! j) $ snd $ Seq.index nssvst i)

checkViewList :: (Eq a, Hashable a) =>
   SuggestionHandlerSimple a ->
   Seq a -> 
   [Seq a] -> 
   TVar (Seq a) -> 
   TVar (Seq (Seq a, [ViewSeqTail a])) ->
   TVar (NextSeq a) ->
   IO [a]
checkViewList sh ts mS tvc tvs tns = do
   cc <- readTVarIO tvc
   cs <- readTVarIO tvs 
   ns <- readTVarIO tns
   let nssvst = viewGeneralLTailUp cc ns
   -- putStrLn $ "Length suggestion: " ++ (Seq.length nssvst)
   if Seq.null ts -- && (and $ Fold.fold $ fmap ((:[]) . and . fmap (Seq.null . withoutappend) . snd) nssvst)
      then do
         lerningS sh tvc tns
         let nssvst2 = viewGeneralLTailUp cc ns
         atomically $ writeTVar tvs nssvst2
	 putStrLn "Lern"
	 return [] -- Nothing
      else do
         -- let nssvst = fmap (\(x,y) fmap (\) y) nssvst'
	 --let hswa = Fold.foldl HMap.union HMap.empty $ fmap (Fold.foldl HMap.union HMap.empty . fmap (\x-> HMap.singleton (suggestion x) (withoutappend x) ) . snd) nssvst
	 let hsswa = Fold.foldl HSet.union HSet.empty $ fmap (Fold.foldl HSet.union HSet.empty . fmap ((\x-> if Seq.null x then HSet.empty else HSet.singleton x) . withoutappend) . snd) nssvst
         let hsSn = Fold.foldl HSet.union HSet.empty $ fmap (\s-> if Seq.null s then HSet.empty else HSet.singleton s) mS
	 let hsswa' = HSet.map (\wa-> Seq.index wa 0) hsswa
	 let hsSn' = HSet.map (\wa-> Seq.index wa 0) hsSn
         atomically $ writeTVar tvs nssvst 
         return $ HSet.toList $ HSet.union hsswa' hsSn'
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

shsStep :: (Eq a, Hashable a, Show a) => 
   SuggestionHandlerSimple a ->
   a -> 
   IO (Maybe a)
shsStep shs a = do
   -- Ben Azai looked and died.
   contextUp (shsCurrentContext shs) (shsMaxContext shs) a
   -- Ben Zoma looked and was damaged [in his mind].
   cs <- checkSuggestion (shsCurrentContext shs) (shsCurrentSuggestion shs)
   --putStrLn "CheckSuggestion"
   --putStrLn $ show cs
   -- Elisha ben Abuya began to “pluck up seedlings” (Maimonides sees in this a desire to comprehend something greater than is possible for human understanding).
   mncs <- updatePowSuggestion (shsPowSuggestion shs) cs
   checkView shs cs mncs (shsCurrentContext shs) (shsCurrentSuggestion shs) (shsCurrentnextSeq shs)
   -- Rabbi Akiva "entered in peace and left in peace."

shsStepList :: (Eq a, Hashable a, Show a) => 
   SuggestionHandlerSimple a ->
   a -> 
   IO [a]
shsStepList shs a = do
   -- Ben Azai looked and died.
   contextUp (shsCurrentContext shs) (shsMaxContext shs) a
   -- Ben Zoma looked and was damaged [in his mind].
   cs <- checkSuggestion (shsCurrentContext shs) (shsCurrentSuggestion shs)
   --putStrLn "CheckSuggestion"
   --putStrLn $ show cs
   -- Elisha ben Abuya began to “pluck up seedlings” (Maimonides sees in this a desire to comprehend something greater than is possible for human understanding).
   mncs <- updatePowSuggestionList (shsPowSuggestion shs) cs
   checkViewList shs cs mncs (shsCurrentContext shs) (shsCurrentSuggestion shs) (shsCurrentnextSeq shs)
   -- Rabbi Akiva "entered in peace and left in peace."

shsInit :: (Eq a, Hashable a, Show a) =>
   Maybe (SuggestionHandlerSimple (Seq a)) ->
   MaxContext -> 
   MaxError ->
   GeneralRadius -> 
   RadiusPattern ->
   IO (SuggestionHandlerSimple a)
shsInit mshss mc me gr rp = do
   tcc <- newTVarIO Seq.Empty
   tcns <- newTVarIO emptyNextSeq
   tcs <- newTVarIO Seq.Empty
   return $ SuggestionHandlerSimple
      tcc tcns tcs mshss mc me rp gr

data StSuggestion a = StSuggestion
   { stsContext :: Seq a
   , stsCurrentSuggestion :: Seq (Seq a, [ViewSeqTail a])
   }

type AdjStSugL a = Env (StSuggestion a)

type AdjStSugR a = Reader (StSuggestion a)

type AdjWStSug a w = W.AdjointT (AdjStSugL a) (AdjStSugR a) w

type CoFreeStSug a w = Cofree ((AdjWStSug a w) :.: List)

initCoFreeStSug :: (Eq a, Hashable a, Show a, Comonad w) =>
   (SuggestionHandlerSimple a, a) -> 
   IO (CoFreeStSug a w a)
initCoFreeStSug p = unfoldM f $ (\(x,y) -> (x,y)) p
   where {-
      f (shs, a) = do
         cc <- readTVarIO $ shsCurrentContext shs
         cs <- readTVarIO $ shsCurrentSuggestion shs
         return $ ((case ma of 
	    Just a -> Seq.singleton a
	    Nothing -> Seq.empty) , (adjEnv (StSuggestion cc cs)) :.: [])-}
      f (shs, a) = do
         cc <- readTVarIO $ shsCurrentContext shs
         cs <- readTVarIO $ shsCurrentSuggestion shs
         la <- shsStepList shs a
         cc' <- readTVarIO $ shsCurrentContext shs
         cs' <- readTVarIO $ shsCurrentSuggestion shs
	 atomically $ writeTVar (shsCurrentContext shs) cc
	 atomically $ writeTVar (shsCurrentSuggestion shs) cs
	 let ls = la
	 return $ (a, Comp1 $ (adjEnv (StSuggestion cc' cs')) $ fmap (\x-> (shs,x)) ls)

treeSug :: CoFreeStSug a w a -> Tree a
treeSug (a :< (Comp1 wla)) = Tree a (fmap treeSug $ extract wla)

