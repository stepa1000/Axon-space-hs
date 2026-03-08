{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.Suggestion where

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
import Control.Concurrent.Async
import Data.Traversable
import Data.Foldable
import Data.Proxy
import Data.UUID
import Data.Sequence as Seq

import Data.Axon.Base.Axon 
   
class HasMemory a i where
  -- reactionTo :: [TArray Int (Maybe (DendritPatern i))] 
  rection :: Lens' a [TArray Int (Maybe (UUID,Set (DendritPatern i)))] 
  -- association :: Lens' a [Set (DendritPatern i)]
  --           Lens' a (TArray Int (Maybe (DendritPatern i)) <-> TArray Int (Maybe (UUID,DendritPatern i))) 
  -- spike :: Lens' a (TArray Int (Maybe (DendritPatern i)) -> TArray Int (Maybe (UUID,DendritPatern i)) )

type EitherPatern i = Either (DendritPatern i) (Set (DendritPatern i))

type AbstPatern a i = TArray Int (Maybe (UUID, EitherPatern i)) 

type CxtAxonMem i w a g = 
   ( CxtAxon i w a g
   , HasMemory a i 
   )
 
addReacrionDP :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   ) => 
--   TArray Int (Maybe (DendritPatern i)) ->
--   TVar Int -> -- localtime
   Float ->
   TArray Int (Maybe (UUID,(DendritPatern i))) ->
   (i,i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   STM Bool
addReacrionDP s aTo pa w = do
   let arr = coask w
   ppi@(xpi,ypi) <- getBounds arr
   a <- readArray arr pa 
   let rea = a^.reaction
   limpt <- getAssocs aTo
   (Or b) <- mapM (\aimpt-> 
      -- limpt <- getAssocs aTo
      absA <- mapArray (fmap (\ (a,b) -> (a,Right b))) aimpt
      (And b) <- mapM (\ (i, muuiddp) -> do
        mept <- readArray absA i
	f ept ansA muuiddp i
	 ) limpt
      b1 <- getBounds aimpt
      b2 <- getBounds aTo
      if (b1 == b2) && b
         then do 
	    mapM (\(i,mpt)->do
	       bi <- getBounds aimpt
	       if inRange bi i
	          then do
	            c <- readArray aimpt i
		    let c2 = (\((uu,sptn))-> mpt >>= (\(uu2,pt)-> Just (uu,insert pt sptn) )) =<< c
	            writeArray aimpt i c2
		    return $ Or True
	          else return $ Or False
	    ) limpt
	 else return $ Or False  
      ) rea
   if (g limpt) && b
      then return b
      else do
         writeArray arr pa (set reaction (aTo : rea) a)
	 return b
   where
      g limpt = not $ length lpt == (size $ fold $ fmap Set.singleton lpt)
         where
	    lpt = join $ fmap (\(_,muupt)-> maybeToList muupt) limpt
      f Nothing _ Nothing _ = return $ And True
      f (uu,(Just (Right spt))) absA (Just (uu2,pt2)) j = do
         (_,y) <- getBounds absA
	 if y >= j then do
	    spt <- fmap fold $ mapM (\ i -> do
	      c <- readArray absA i 
	      (b,c2) <- case c of
	         Nothing -> return (True, Nothing)
	         (Just (uu3, Right spt3) ) -> return ((spt3 == spt) && (uu3 == uu) , Just (uu2,Left pt2))
	         (Just (uu3, Left pt3) ) -> return ((pt3 == pt2) && (uu3 == uu2) , Just (uu2,Left pt2))
	      writeArray absA i c2
	      return $ And b
	      else return $ And False -- Maybe False ????????????
	   ) (range (j,y))
	 return spt
      f (uu,(Just (Left pt))) absA (Just (uu2,pt2)) j = if pt == pt2 then return $ And True else return $ And False
      f _ _ _ _ = return $ And False
	
   -- mapArray aTo
   -- writeArray arr pa (set reaction (aTo : rea) a)
   {-aNil <- newArray (fromInteger 0, fromInteger 0) Nothing
   a <- readArray arr pa
   let fp = a^.reaction
   writeArray arr pa (set reaction (f fp) a)
   where
      f fp = 
         (\ aTl -> if aTl == aTo then aFrom else (biTo fp) aTl) :<->: 
         (\ aTu -> if aTu == aFrom then aTo else (biFrom fp) atu)  -}

sensPatern :: Float -> DendritPatern i -> DendritPatern i -> Bool
sensPatern s dp1 dp2 = (realToFrac x)/(realToFrac l) > s
   where
      (Sum x) = foldMap (\p-> if member p dp2 then Sum 1 else Sum 0) dp1
      l = max (size dp1) (size dp2)

distancePatern :: DendritPatern i -> DendritPatern i -> Int
distancePatern dp1 dp2 = x
   where
      (Sum x) = foldMap (\p-> if member p dp2 then Sum 1 else Sum 0) dp1

updateReactionDP ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   ) =>
   Float -> 
   TArray Int (Maybe (UUID, Set (DendritPatern i))) ->
   (i,i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   STM [TArray Int (Maybe (UUID,Set (DendritPatern i)))]
updateReactionDP s ta p w = do
   let arr = coask w
   ppi@(xp,yp) <- getBounds arr
   a <- readArray arr p
   let rea = a^.reaction 
   fmap catMaybes $ mapM (\ atn -> do
      ppi2@(xpi2,ypi2) <- getBounds atn 
      let latn = rangeSize ppi2
      ltn <- getAssocs atn
      lT <- fmap (getSum . fold) $ mapM (\ (i,muuidsdp) -> do
         muuiddp2 <- readArray ta i
	 return $ if maybe False id (f muuidsdp muuiddp2) then Sum 1 else Sum 0 -- False
	 ) ltn
      let t = (realToFrac lT)/(realToFrac latn)
      if t > s then return $ Just ltn
               else return Nothing
      ) rea
   where
      f Nothing Nothing = return True
      f m1 m2 = do
         uuiddp@(uu1,dp) <- m2
	 uuidsdp@(uu2,sdp) <- m1
	 return $ if (uu1 == uu2) && (not $ null $ filter (\ p -> member p dp) adp)
      f _ _ - Nothing
         

class HasUpdateMemory a i where
  -- reactionTo :: [TArray Int (Maybe (DendritPatern i))] 
  --updateStep :: Lens' a Int
  --updateStepLength :: Lens' a Int
  updateCurrentMemUp :: Lens' a [(Int,TArray Int (Maybe (UUID,Set (DendritPatern i))))]  
--                            Curent Step
--

midleDP :: Num i => DendritPatern i -> (i,i)
midleDP dp = f $ fold $ map (\(x,y)-> (Max x,Min x, Max y, Min y)) dp
   where
      f (maxX,minX,maxY,MinY) = ((maxX - minX / (realToFrac 2)) + minX ,(maxY - minY / (realToFrac 2)) + minY )

type FreeSpace = TVar Bool

seeDendrit ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , HasUpdateMemory a i
   ) =>
   TVar Int -> -- localtime
   Float -> -- step wave Dendrit space
--   w () ->
   ( Int ->
     DendritPatern i ->
     UUID ->
     Bool ->
     W.AdjointT 
        (AdjArrayL (i,i) a)
        (AdjArrayR (i,i) a)
        w
        b ->
     IO ()
   ) -> 
   [(i,i)] -> -- updating
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
--   FreeSpace -> 
--   UUID -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
seeDendrit lt ts f lu hma w = do
   let arr = coask w
   mapM (\ p ->
      a <- readArray arr p 
      let lupt = a^.updateCurrentMemUp 
      lupt2 <- fmap join mapM (\ (cs,apt) -> do
         muusdp <- readArray apt cs
	 mapM_ (\ (uu,sdp) ->
	    let mnarr = HMap.lookup uu hma
	    mapM_ (\(narr,fs)-> do
	       let wn = adjEnv narr (lower w)
	       t <- atomicaly $ do
	          b <- readTaVar fs
                  -- b2 <- readTaVar fs2
		  check b 
		  writeTVar fs False
                  modifyTVar lt (+1)
		  readTVar lt
	       mapM_ (\ dp -> do
	          atomicaly $ do
		     writeDendritPatern dp wn
		  updateDedritSpace t st (midleDP dp) (f dp uu False wn)
		  ) sdp
	       -- f (Set.empty) uu True wn
	       atomicaly $ do 
	          writeTVar fs True
		   lt
	       ) mnarr
	    ) muusdp
         ppi@(xp,yp) <- getBounds apt -- arr ???????????
	 return $ if inRange ppi (s+1) then [(s+1,apt)] else []
	 ) lupt
      writeArray arr p (set updateCurrentMemUp lupt2 a)
      ) lu

seeDendritALL ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , HasUpdateMemory a i
   ) =>
   TVar Int -> 
   Float ->
   w () ->
   ( Int ->
     DendritPatern i ->
     UUID ->
     Bool ->
     W.AdjointT 
        (AdjArrayL (i,i) a)
        (AdjArrayR (i,i) a)
        w
        b ->
     IO ()
   ) -> 
   HashMap UUID [(i,i)] -> -- updating
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
   IO ()
seeDendritALL lt s f w0 hup hta = do
   mapConcurrently_ (\ (uu,(ta,_)) -> 
      let wn = adjEnv ta w0 
      let lp = join $ maybeToList $ HMap.lookup uu hup 
      seeDendrit lt s f lp hta wn
      -- f (Set.empty) uu True wn
      ) (toList hta)
   t <- readTVarIO lt
   mapConcurrently_ (\ (uu,(ta,_)) ->
      let wn = adjEnv ta w0 
      f t (Set.empty) uu True wn
      ) (toList hta) 
   atomicaly $ writeTVat lt 0

class SensDendrit a i where
   sensD :: Lens' a (TArray Int (Maybe (UUID, Set (DendritPatern i))))
   nowSense :: Lens' a (Set (DendritPatern i))
   stepSense :: Lens' a Int
   maxStepSens :: Lens' a Int
   --sensePoint :: Lens' a (i,i)
   senseRadius :: Lens' a i

senseDendritRead ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   Int ->
   Float -> -- semi
   HashMap UUID (Set (i,i)) -> -- Read Active
   TQueue (UUID,DendritPatern i,(i,i),Int ) ->
   HashMap UUID [(i,i)] -> 
   DendritPatern i ->
   UUID ->
--   Bool ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
senseDendritRead t s ractive queRA sensor ndp uu w = do
   let lp = join $ maybeToList $ HMap.lookup uu sensor
   mapM (\ p -> do
      let arr = coask w 
      a <- readArray arr p 
      dp <- readDendritPatern p (a^.senseRadius) w -- (a^.sensePoint)
      if dp == ndp then return ()
         else do
	    -- let sd = a^.sensD
	    let ns = a^.nowSense
	    writeArray arr p (set nowSense ((Set.singletone dp) <> ns) a)
	    let msetAct = HMap.lookup uu ractive
	    mapM (\setAct -> do
	       if Set.member p setAct
	          then atomicaly $ writeTQueue queRA (uu,dp,p,t)
	       ) msetAct
      ) lp

-- type BSuggestion = Bool

type QueueReception i = TQueue (UUID,DendritPatern i,(i,i),Int ) 

type QueueLerned i = TQueue (UUID,(i,i))

type QueueReacting i = TQueue (UUID,(i,i)) 

senseDendrit ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   Int ->
   Float -> -- semi
   HashMap UUID (Set (i,i)) -> -- Read Active reception
   QueueReception i -> -- reception
   QueueLerned i -> -- lerned 
   QueueReacting i ->
   HashMap UUID (Set (i,i)) -> -- updateing
   DendritPatern i ->
   UUID ->
   Bool ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
senseDendrit lt s ractive queRA _ _ sensor ndp uu False w = 
   senseDendritRead lt s ractive queRA sensor ndp uu w  
senseDendrit lt s ractive _ queLerned queReacting sensor ndp uu True w = do
   let lp = join $ maybeToList $ HMap.lookup uu sensor
   mapM (\ p -> do
      let arr = coask w 
      a <- readArray arr p 
      --dp <- readDendritPatern (a^.sensePoint) (a^.senseRadius) w
      --if dp == ndp then return ()
      --  else do
      let sd = a^.sensD
      let ns = a^.nowSense
      let i = a^.stepSense
      let mi = a^.maxStepSens
      let msetAct = HMap.lookup uu ractive
      {-
      mapM (\setAct -> do
         if Set.member p setAct
         then atomicaly $ writeTQueue queRA (uu,ns,p)
	 ) msetAct
      -}
      lipt <- getAssocs sd
      ppi@(xp,yp) <- getBounds sd
      nsd <- newArray_ (xp,i)
      mapM (\j-> do
	      if j == i
	         then if (not $ Set.nil ns) then writeArray nsd j (Just (uu,ns))
		         else writeArray nsd j Nothing 
		 else do
	            aj <- readArray sd j
	            writeArray nsd j aj
	      ) (if i <= mi then range (xp,i) else range (xp,mi))
      if i == mi 
         then do
	      ldp <- updateReactionDP s nsd p w
              arr0 <- newArray_ (0,0)
	      if length ldp > 0
	         then do
		    let bSetP = maybe False (\setP-> Set.member p setP) $ HMap.lookup uu ractive
                    if bSetP 
		       then do
		         writeArray arr p 
	                    ( ( set stepSense 0
	                        set nowSense Set.empty .
	                        set sensD arr0 . 
		                ) a) 
		       else do
		          atomicaly $ writeTQueue queReacting (uu,p)
	                  let ucmu = a^.updateCurrentMemUp
	                  let lr = filter (\e-> not $ elem e ldp) (a^.rection)	 
                          writeArray arr p 
	                     ( ( set stepSense 0
	                         set nowSense Set.empty .
	                         set sensD arr0 . 
		                 set updateCurrentMemUp (lr ++ ucmu)) a)
	         else do
	            let lr = (a^.rection) 
        	    if length lr < 0 
		       then do
		          atomicaly $ writeTQueue queLerned (uu,p)
		          writeArray arr p 
		             ( ( set stepSense 0 .
                                 set sensD arr0 .
                                 set nowSense Set.empty .
			         set reaction [nsd]
		             ) a) 
	               else writeArray arr p 
		            ( ( set stepSense 0 .
                                set sensD arr0 .
                                set nowSense Set.empty 
		              ) a) 
	 else do
	    writeArray arr p 
		    ( ( set stepSense (i + 1) .
                        set sensD nsd .
                        set nowSense Set.empty 
		        ) a) 
--      if Set.member p ractive
--         then return [ndp]
--	 else return []
      ) lp
--   atomicaly $ writeTVat lt 0

data SuggestionSafe i = SuggestionSafe
   { safeSenseD :: (TArray Int (Maybe (UUID, Set (DendritPatern i)))) 
   , safeStepSense :: Int 
   , safeCurentMemUp :: [(Int,TArray Int (Maybe (UUID,Set (DendritPatern i))))]
   -- , safePoint :: (i,i)
   }

class Suggestion a i where
   safeSuggestion :: Lens' a (Cofree (HashMap [Signal i] ) (SuggestionSafe i))
   suggestionStart :: Lens' a Int
   -- safeMaxDepth :: Lens' a Int
   --

type SuggestionPath i = Seq (Set (SignalA i))

suggestionSafe ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   -- [(UUID,(i,i))] ->
   Set (i,i) -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
suggestionSafe sp lpUp w = do
   let arr = coask w 
   mapM (\p-> do 
      a <- readArray arr p
      let ss = a^.suggestionStart
      let safeCo = g a (drop ss sp) $ a^.safeSuggestion 
      writeArray arr p (set safeSuggestion safeCo a)
      ) lpUp
   where
      g a (p:sp) sco@(b :<| _) = if (HMap.nil fnsco) && (nil sp) -- ???? ||
            then b :< (HMap.insert p ((SuggestionSafe
	       (a^.senseD)
	       (a^.stepSense)
	       (a^.updateCurrentMemUp)
	       ) :< (HMap.empty)) fnsco)
	    else (HMap.alter (\ mnsco -> (do 
	       nsco <- mnsco
	       return $ g sp nsco
	       ) <|> (
               return $ (SuggestionSafe
	          (a^.senseD)
	          (a^.stepSense)
	          (a^.updateCurrentMemUp)
	          ) :< (HMap.empty)
	       )
	       ) p fnsco)-}
         where
	    fnsco = unwrap sco

suggestionSafeAll ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   -- [(UUID,(i,i))] ->
   HashMap UUID (Set (i,i)) -> 
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
   w () ->
   IO () -- [DendritPatern i]
suggestionSafeAll spath act lpUp w0 = do
   mapConcurrently_ (\ (uu,(ta,_)) -> 
      let wn = adjEnv ta w0 
      let sp = join $ maybeToList $ HMap.lookup uu act
      suggestionSafe sppath sp act wn
      ) lpUp
   

suggestionReSafe ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   Set (i,i)-> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
suggestionReSafe sp act lpUp w = do
   let arr = coask w 
   mapM (\p-> do 
      a <- readArray arr p
      let msugg = g sp $ a^.safeSuggestion 
      let ss = a^.suggestionStart
      mapM (\sugg-> do
         if length sp > ss 
	    then
               writeArray arr p (
	          ( set senseD (safeSenseD sugg) .
	            set stepSense (safeStepSense sugg) .
	            set updateCurrentMemUp (safeCurentMemUp sugg)
	          ) a)
	    else return ()
         ) msugg
      ) lpUp
   where
      g [] (o :< fsco) = return o
      g (p:sp) (o :< fsco) | HMap.null fsco = return o
      g (p:sp) sco = (HMap.lookup p fnsco) >>= (\nsco-> g sp nsco)
         where
	    fnsco = unwrap sco

suggestionReSafeAll ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   HashMap UUID (Set (i,i)) -> 
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
   w () ->
   IO () -- [DendritPatern i]
suggestionReSafeAll spath act lpUp w0 =
   mapConcurrently_ (\ (uu,(ta,_)) -> 
      let wn = adjEnv ta w0 
      let sp = join $ maybeToList $ HMap.lookup uu act
      suggestionReSafe spath sp act wn
      ) lpUp

suggestionUpdate ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   SuggestionPath i -> 
   [(i,i)] -> 
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () -- [DendritPatern i]
suggestionUpdate sp ui w = do


activationD ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   [Signal i] -> -- Active
   HashMap UUID (TArray (i,i) a, FreeSpace) -> 
   IO ()
activationD lact hmTa = do
   mapM (\ (uu,sdp,p,_) -> do
      marr <- HMap.lookup uu hmTa
      mapM (\arr-> do
         a <- readArray arr p 
	 -- let r = a^.rection
	 -- let upR = a^.updateCurrentMemUp
	 narr <- newArray (0,0) (Just (uu,sdp))
         writeArray arr p (
	    ( set updateCurrentMemUp [(0,narr)] .
	      set maxStepSens 0
	    ) a
	    ) -- ((fmap (\x-> (0,x)) r) ++ upR))
	 ) marr
      ) lact

readActiveFrequent :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   TQueue (Signal i) ->
   IO (HashMap (Signal i) (Sum Int ) )
readActiveFrequent queue = do
   ls <- atomicaly $ flushTQueue queue
   return $ foldl (\ hm1 hm2 -> unionWith <> hm1 hm2) HMap.empty $ 
      fmap (\(uu,dp,pi,_) -> HMap.singletone (uu,dp,pi) (Sum 1) ) ls

readActive :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , SensDendrit a i
   ) =>
   TQueue (Signal i) ->
   IO [HashMap (SignalKey i) (SignalElem i) ]
readActive queue = do
   ls <- atomicaly $ flushTQueue queue 
   let ms = fold $ fmap (\(uu,dp,ip,t)-> Map.singletone t (HMap.signgletone (uu,ip) dp) ) ls
   if not $ nil ls
      then 
         let (minT,minS) = findMin ms
         let (maxT,maxS) = findMax ms
	 f minT maxT ms []
   where
      f i1 i2 ms l | i1 <= i2 = (do
            (t,hmkdp1) <- mts
            (hmkdp2,ln) <- uncons l
            let lk = keys hmkdp1 
	    if or (fmap (\k-> HMap.member k hmkdp2) lk)
	       then f (t+1) i2 ms (hmkdp1:hmkdp2:ln)
	       else f (t+1) i2 ms ((HMap.union hmkdp1 hmkdp2):ln)
	    ) 
        where
	   mts = lookupGE i1 ms
     f i1 i2 ms [] | i1 <= i2 = (do
            (t,hmkdp1) <- mts
	    f (t+1) i2 ms ([hmkdp1])
	    ) 
        where
	   mts = lookupGE i1 ms
     f _ _ _ l = return l

hmSignalToSetSignalA :: HashMap (SignalKey i) (SignalElem i) -> Set (SignalA i)
hmSignalToSetSignalA hm = fold $ fmap (\((uu,ip),dp)-> Set.singletone (uu,dp,ip) ) HMap.toList

type BSuggestion = Bool

dendritStepCycle' ::     
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , HasUpdateMemory a i
   ) =>
   Float -> -- step wave Dendrit space
   Float -> -- semi sense
   HashMap UUID (Set (i,i)) -> -- Read Active
   QueueReception i -> -- reception
   QueueLerned i -> -- lerned 
   QueueReacting i ->
   HashMap UUID [(i,i)] -> -- Sense upda
   w () -> 
   HashMap UUID [(i,i)] -> -- updating
   HashMap UUID (TArray (i,i) a, FreeSpace) ->
   IO ()
dendritStepCycle' stw semiS hmrAct quAct qL qR hmUpS w0 hmUpD hmArrFS = do
   seeDendritALL stw w0 
      ( senseDendrit semiS hmrAct quAct qL qR hmUpS
      ) hmUpD hmArrFS

type SignalKey i = (UUID,(i,i))

type SignalElem i = DendritPatern i 

type Signal i = (UUID, DendritPatern i, (i,i), Int) 
-- QueueReception i = TQueue (UUID,DendritPatern i,(i,i),Int ) 

type SignalA i = (UUID, DendritPatern i, (i,i))

data DendritSC i a = DendritSC
   { stepWave :: Float
   , semiSense :: TVar Float
   , readActiveDSC :: HashMap UUID (Set (i,i))
   , queueActive :: QueueReception i 
   , queueLerned :: QueueLerned i
   , queueReacting :: QueueReacting i  
   , sensorHM :: TVar (HashMap UUID (Set (i,i)) )
   , reactionHM :: TVar (HashMap UUID (Set (i,i)) )
   , lernHM :: TVar (HashMap UUID (Set (i,i)) ) 
   , fieldHM :: TVar (HashMap UUID (TArray (i,i) a, FreeSpace))
   , readNextSignal :: IO (Set (SignalA i))
   , writeSuggestion :: Set (SignalA i) -> IO () -- Bool DendritPatern 
   , suggestionPast :: TVar Free (HashMap (Set (SignalA i))) ()
   , midleSignal :: TVar (SuggestionPath i)
   , suggestionError :: TVar Float
   --, midleSignalPast :: TVar Int
   -- , midleSignalPow2 :: TVar ([[Signal i]],[[Signal i]])
   , signalContext :: TVar (SuggestionPath i)
   -- , alwaysSensorReaction :: TVar (HashMap UUID (Set (i,i)))
   , maxSuggestion :: Int
   , maxSContext :: Int
   }

distanceSignal :: SuggestionPath i -> SuggestionPath i -> Int
distanceSignal ls1 ls2 = getSum $ fold $ zipWith (\s1 s2 -> if s1 == s2 then Sum 1 else Sum 0) ls1 ls2

filterSuggestionPast :: Int -> SuggestionPath i -> Free (HashMap (Set (Signal i))) () -> Free (HashMap (Set (Signal i))) ()
filterSuggestionPast dist ls hms = fst $ g ls hms (Sum 0)
   where
      g Seq.Empty fhsm s = (fhsm,s)
      g ls (Free hmsn) s = fold fmap (\(k,hm)-> HMap.singletone k hm) $ fmap (\ (k,fhm) -> 
         let mlns = Seq.unsnoc ls
	 in fmap (\(ln,ns) -> if ns == k 
	    then let
	       (f,sU) = g ln fhm (s <> (Sum 1))
	       in if dist <= (getSum sU)
	          then (HMap.singletone k f, sU)
		  else (HMap.empty, sU)
	    else let
               (f,sU) = g ln fhm (s <> (Sum 0))
	       in if dist <= (getSum sU)
	          then (HMap.singletone k f, sU)
		  else (HMap.empty, sU)
	    ) mlns
	 ) $ toList hmsn 
      g _ (Pure ()) s = (Pure (), s)

lengthSuggestion :: Free (HashMap (Set (Signal i))) () -> Int -> Int
lengthSuggestion (Pure ()) s = s
lengthSuggestion (Free fhms) s = getMax $ fold $ map (\(_,fhm2)-> Max $ lengthSuggestion fhms (s+1) ) $ toList fhms

midleSuggestion' :: Free (HashMap (Set (Signal i))) () -> [SuggestionPath i]
midleSuggestion' (Pure ()) = [Seq.Empty]
midleSuggestion' (Free hm) = map (\ (k,fhm) -> fmap (k :) (midleSuggestion fhm) ) $ toList hm

type SuggestionOption i = [Set (SignalA i)]

mapMSuggestion :: Monad m =>  
   (SuggestionPath i -> SuggestionOption i )-- m (Free (HashMap (Set (Signal i))) ()) ) -> 
   SuggestionPath i -> 
   Free (HashMap (Set (Signal i))) ()  -> 
   m (Free (HashMap (Set (Signal i))) () )
mapMSuggestion f ck (Free hm) = fmap Free $ traverseWithKey  (\k fhm -> do
   fhmN <- mapMSuggestion f (ck :>| k) fhm
   return fhmN
   ) fhm 
mapMSuggestion f ck (Pure ()) = do
   so <- f ck
   return $ Free $ fold $ map (\k-> HMap.singletone k (Pure ())) so --ck :>| k 
   -- return so -- Free $ fold $ map (\k-> HMap.singletone (ck :>| k) (Pure ())) so

midleSuggestion :: Free (HashMap (Set (Signal i))) ()  -> SuggestionPath i
midleSuggestion f = fmap fst $ foldl (\ (ls,t) (k,Max ma2, Min mi2) -> 
         if t < (ma2 - mi2) then (ls,t) else (k, ma2 - mi2) ) ([[]], maxBound) $ 
      HMap.toList $ foldl (\hm hm2 -> unionWith <> hm hm2) HMap.empty $ do
         s1 <- ls
         s2 <- ls
         let dist = distanceSignal s1 s2
         guard $ not $ dist == (length s1)
         return ((HMap.singletine s1 (Max dist,Min dist)) <> (HMap.singletone s2 (Max dist, Min dist)) )
   where
      ls = midleSuggestion' f

nextSuggestion ::
   Free (HashMap (Set (Signal i))) ()  -> 
   (Free (HashMap (Set (Signal i))) () ) -- suggestion missing !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! with eq keys
nextSuggestion (Pure ()) = Pure ()
nextSuggestion (Free hm) = foldl (unionWith <>) $ fmap (\ fhm -> case fhm of
   (Free hm2) -> hm
   (Pure ()) -> HMap.empty ) $ HMap.toList hm
--   where
--      nsug (Free hm1) = 

type AdjDendritSCL i a = Env (DendritSC i a)

type AdjDendritSCR i a = Reader (DendritSC i a)

type LernFlag = Bool

dendritSCIO ::      
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxonMem i w a g
   , HasUpdateMemory a i
   ) =>
   ( LernFlag -> 
     Set (SignalA i) ->
     TVar Float -> -- Semi
     TVar (HashMap UUID (Set (i,i)) ) -> -- sensor
     QueueLerned i ->
     QueueReacting i ->
     TVar (HashMap UUID (Set (i,i)) ) -> -- lern
     TVar (HashMap UUID (Set (i,i)) ) -> -- reaction
     TVar (HashMap UUID (TArray (i,i) a, FreeSpace)) ->
     IO Bool
   ) ->
   ( IO 
   ) ->
   W.AdjointT 
      (AdjDendritSCL i a)
      (AdjDendritSCR i a)
      w
      b ->
   IO ()
dendritSCIO mindC w = do
   let dsc = coask w 
   cSignal <- (readNextSignal dsc)
   fhm0 <- readTVarIO (fieldHM dsc)
   semiS0 <- readTVarIO (semiSense dsc)
   hmS0 <- readTVarIO (sensorHM dsc)
   hmU0 <- readTVarIO (reactionHM dsc)
   hmArr0 <- readTVarIO (fieldHM dsc)
   -- suggestionSafe
   sc <- readTVarIO (signalContext dsc)
   mids <- readTVarIO (midleSignal dsc)
   --(midSP1,midSP2) <- readTVarIO (midleSignalPow2 dsc) 
   suggP <- readTVarIO (suggestionPast dsc)
   let scn = cSignal :<| sc
   --let distMiddle = distanceSignal scn mids
   --let distMiddleP1 = distanceSignal scn midSP1
   --let distMiddleP2 = distanceSignal scn midSP2
   let fSugg = filterSuggestionPast distMiddle scn suggP
   let lengthSCN = length scn  
   let midleN = midleSuggestion fSugg
   --midP <- readTVarIO (midleSignalPast dsc)
   let distMiddle = distanceSignal scn midleN
   se <- readTVarIO (suggestionError dsc)
   let be = (realToFrac distMidle) / (realToFrac lengthSCN) < se
   if ((\fs -> case fs of
         (Pure ()) -> True
	 (Free fm) -> (HMap.nil fm) || (lengthSuggestion midleN < (maxSuggestion dsc))
         ) fSugg) -- || be
      then do
         fSuggN <- f dsc (lengthSuggestion midleN) (maxSuggestion dsc)
         atomicaly $ writeTVar (suggestionPast dsc) fSuggN
	 let midleNOut@(a :<| s) = midleSuggestion fSuggN
	 let (a :<| s) = z 0 (lengthSCN + 1) midleNOut
	 atomicaly $ writeTVar (midleSignal dsc) midleNOut
	 atomicaly $ writeTVar (signalContext dsc) $ nextSC scn (maxSContext dsc)
         (writeSuggestion dsc) a
	 --let midleNOutN = midleNOut 
      else if be
         then do
	    -- suggestionReSafeAll Seq.Empty (unionWith <> hmS0 hmU0) hmArr0 (lower w)
	    g dsc scn
	    atomicaly $ writeTVar (signalContext dsc) $ nextSC scn (maxSContext dsc)
	 else  
	    fSuggN <- fmap nextSuggestion $ f dsc (lengthSuggestion midleN) (maxSuggestion dsc)
            atomicaly $ writeTVar (suggestionPast dsc) fSuggN
	    let midleNOut@(a :<| s) = midleSuggestion fSuggN
	    let (a :<| s) = z 0 (lengthSCN + 1) midleNOut
	    atomicaly $ writeTVar (midleSignal dsc) midleNOut
	    atomicaly $ writeTVar (signalContext dsc) $ nextSC scn (maxSContext dsc)
            (writeSuggestion dsc) a
   where
      nextSC (sc :|> a) l | (length sc) >= l = a :<| (nextSC sc l) 
      nextSC _ _ = Seq.Empty 
      --z _ _ Seq.Empty = Seq.Empty
      z i j (s :|> a) | i < j = a :<| (z (i+1) j s)
      z _ _ Seq.Empty = Seq.Empty
      --z i j (s :|> a) | i < j = a :<| (z (i+1) j s)
      g dsc Seq.Empty _ = return ()
      g dsc (s :|> a) ck = do
         lsRec <- untilJustM $ do
            semiS <- readTVarIO (semiSense dsc)
            hmS <- readTVarIO (sensorHM dsc)
	    hmL <- readTVarIO (lernHM dsc)
            hmU <- readTVarIO (reactionHM dsc)
            hmArr <- readTVarIO (fieldHM dsc) 
            suggestionReSafeAll ck (unionWith <> hmS hmU) hmArr0 (lower w)
            activationD a hmArr
            dendritStepCycle' 
               (stepWave dsc) semiS (readActiveDSC dsc) (queueActive dsc) (queueLerned dsc) (queueReacting dsc)
	       (unionWith <> hmS hmL) (lower w) hmU hmArr
            sreceptionHM <- readActive (readActiveDSC dsc)
            let lsRecept = fmap hmSignalToSetSignalA sreceptionHM
            bMind <- mindC True
	       lsRecept (semiSense dsc) (sensorHM dsc) (queueReacting dsc) (queueLerned dsc) (lernHM dsc) (reactionHM dsc) (fieldHM dsc) 
	    if bMind 
	       then return $ Just lsRecept
	       else Nothing
	 hmS <- readTVarIO (sensorHM dsc)
         hmU <- readTVarIO (reactionHM dsc)
         hmArr <- readTVarIO (fieldHM dsc) 
	 suggestionSafeAll (a :<| ck) (unionWith <> hmS hmU) hmArr 
	 g dsc (s) (a :<| ck)
      f dsc nlen maxLen fSuggN | nlen <= maxLen = f dsc (nlen + 1) maxLen $
         mapMSuggestion (\ kp -> do
	    lsAct <- untilJustM $ do
	       --cSignal <- (readNextSignal dsc)
               --fhm <- readTVarIO (fieldHM dsc)
               semiS <- readTVarIO (semiSense dsc)
               hmS <- readTVarIO (sensorHM dsc)
               hmU <- readTVarIO (reactionHM dsc)
               hmArr <- readTVarIO (fieldHM dsc)
               suggestionReSafeAll kp (unionWith <> hmS hmU) hmArr (lower w)
               when (Seq.nil kp) $ activationD cSignal hmArr
               --when (not $Seq.nil kp) $ activationD ((\(_ :>| k)->k) kp) hmArr
               dendritStepCycle' 
                  (stepWave dsc) semiS (readActiveDSC dsc) (queueActive dsc) (queueLerned dsc) (queueReacting dsc)
		  hmS (lower w) hmU hmArr
	       sactiveHM <- readActive (readActiveDSC dsc) 
	       -- atomicaly $ flushTQueue (queueLerned dsc) 
	       -- atomicaly $ flushTQueue (queueReacting dsc) 
	       let lsAct = fmap hmSignalToSetSignalA sactiveHM
               bMind <- mindC False
	          lsAct (semiSense dsc) (sensorHM dsc) (queueReacting dsc) (queueLerned dsc) (lernHM dsc) (reactionHM dsc) (fieldHM dsc) 
	       if bMind 
	          then return $ Just lsAct
		  else Nothing
	    hmS <- readTVarIO (sensorHM dsc)
            hmU <- readTVarIO (reactionHM dsc)
            hmArr <- readTVarIO (fieldHM dsc) 
	    mapM (\ sAct -> do 
	       suggestionSafeAll (sAct :<| kp) (unionWith <> hmS hmU) hmArr 
	       ) lsAct -- OPTINIZE THE .... !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	    -- let distKP = distanceSignal 
	    -- let maxS = foldl1 (\ (s1,Sum n1) (s2,Sum n2) -> if n1 > n2 then (s1,Sum n1) else (s2,Sum n2) ) $ HMap.toList sactive
	    return lsAct
	    )
      f _ _ _ _ = return ()
{-
data DendritSCS i a = DendritSCS
   { stepWave :: Float
   , semiSense :: TVar Float
   , readActiveDSC :: HashMap UUID (Set (i,i))
   , queueActive :: TQueue (Signal i) 
   , sensorHM :: TVar (HashMap UUID (Set (i,i)) )
   , reactionHM :: TVar (HashMap UUID (Set (i,i)) )
   , fieldHM :: TVar (HashMap UUID (TArray (i,i) a, FreeSpace))
   , readNextSignal :: IO (Set (Signal i))
   , writeSuggestion :: Set (Signal i) -> IO () -- Bool DendritPatern 
   --, suggestionPast :: TVar Free (HashMap (Set (Signal i))) ()
   --, midleSignal :: TVar (SuggestionPath i)
   --, suggestionError :: TVar Float
   --, midleSignalPast :: TVar Int
   -- , midleSignalPow2 :: TVar ([[Signal i]],[[Signal i]])
   --, signalContext :: TVar (SuggestionPath i)
   -- , alwaysSensorReaction :: TVar (HashMap UUID (Set (i,i)))
   --, maxSuggestion :: Int
   }

dendritSCSimple :: 
-}
         

 {-  where
      suggZero = do
         activationD cSignal freadActivehm
         dendritStepCycle' 
            (stepWave dsc) semiS (readActiveDSC dsc) (queueActive dsc) hmS (liwer w) hmU hmArr
-}        
   -- readActive
   


