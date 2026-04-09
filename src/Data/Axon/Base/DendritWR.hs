{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.DendritWR where

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

import Data.Axon.Base.Axon

type QueueWriteDP i = TQueue [DendritPatern i]

type QueueReadDP i = TQueue [(DendritPatern i,(i,i))] -- (i,i)

-- type PointAndR i = ((i,i),i)

-- type WaveStep = Float 

dendritWriteRead ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   WaveStep ->
   QueueWriteDP i ->
   QueueReadDP i ->
   [PointAndR i] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
dendritWriteRead s quW quR lP w = do
   lldp <- atomicaly $ flushTQueue quW 
   let lldpp = (fmap . fmap) (\dp-> (dp, midleDP dp)) lldp
   mapM (\ldpp-> do
      mapM (\(dp,_)-> writeDendritPatern dp w) ldpp
      updateDedritSpace s (fmap snd ldpp) 
         ( \ wn -> do
	    ldpOut <- mapM (\ (ip,i) -> do
	       dpn <- readDendritPatern ip r
	       return (dpn,ip)
	       ) lP
	    atomicaly $ writeTQueue quR ldpOut
	 ) w
      ) lldpp

type PointLinearMemory i = PointAndR i 

type QueuePLM i = TQueue (PointLinearMemory i)

type SeqLM i = Seq (DendritPatern i, PointAndR i)

dendritLinearMemory ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   TVar (SeqLM i) ->
   WaveStep ->
   QueueWriteDP i ->
   -- QueueReadDP i ->
   QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
dendritLinearMemory tvsDP s quW quPLM w =
   lPLM <- atomicaly $ flushTQueue quPLM
   lldp <- atomicaly $ flushTQueue quW
   mapM (\ (plm,ldp) -> do
      quWdp <- newTQueueIO 
      quRdp <- newtQueueIO
      atomivaly $ do
         writeTQueue quWdp ldp
	 -- writeTQueue quRdp
      dendritWriteRead s quWdp quRdp [plm] w
      atomicaly $ do
         lrdp <- flushTQueue quRdp
         modifyTVar tvsDP (\sdp-> sdp :>| (head lrdp)) -- plm
      ) $ zip lPLM lldp
   
 
dendritReactLinearMemory ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   SeqLM i -> -- TVar (SeqLM i) ->
   WaveStep ->
   QueueWriteDP i ->
   QueueReadDP i ->
   -- QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (Seq Bool)
dendritReactLinearMemory sdpp s quW quR w =
   -- sdpp <- readTVarIO tvsDP 
   let lpr = fold $ fmap ( (: []) . snd) sdpp
   dendritWriteRead s quW quR lpr w
   seqrdp <- fmap (foldl (\ b a -> b :>| (fold $ fmap HSet.singletone a)) Seq.empty) $ atomicaly $ flushTQueue quRdp
   return $ Seq.zipWith (\ (dp,pr) hsDp -> HSet.member (dp,pr) hsDp) sdpp seqrdp

type HMDPf i = HashMap (DendritPatern i, PointAndR i) Int 

-- frequncy generalization for reception

frequencyLinearMemoryHMDP :: SeqLM i -> HMDPf i
frequencyLinearMemoryHMDP slm = fmap getSum $ foldl1 (unionWith (<>)) $ fmap (\(dp,pr)-> HMap.singletone (dp,pr) (Sum 1) ) slm

type MFDP i = Map Int (HeshSet (DendritPatern i, PointAndR i))

frequencyLMMF :: HMDPf i -> MFDP i
frequencyLMMF hmdpf = foldl1 (Map.unionWith (<>)) $ HMap.mapWithKey (\ k fr -> Map.singletone fr (HSet.singletone k)) hmdpf

seqToFrequency :: SeqLM i -> MFDP i 
seqToFrequency = frequencyLMMF . frequencyLinearMemoryHMDP 

type PatternRadius = Int

generationPattern :: PatternRadius -> SeqLM i -> HashSet (SeqLM i)
generationPattern pr slm = hsslm 
   where
      hsslm = foldl1 (<>) $ map (i->let
         li = [ x | x >= 0, x < (Seq.length slm), x <- [i-pr, i-pr +1 .. i+pr]]
         in HSet.singletone $ foldl1 (<>) $ map (\j-> Seq.singletone (index slm j)
	    ) li
	 ) lei
      lei = join $ map (\dppr@(dp,pointR)-> let
         in Seq.elemIndicesR slm dppr
	 ) lfreMidleMax
      mfre = seqToFrequency slm
      mmaxFre = Map.lookupMax mfre
      lfreMidleMax = join $ maybeToList $ map (\(k,a)-> let
         midK = k / 2 -- maybe 80/20, 20/80 Pareto. The parametor
	 in fold $ fmap (\x->[x]) $ Map.filterKeys (\nk-> nk > midK) mfre
	 ) mmxaFre
-- end frequncy generalization for reception
{-distanceSeq :: Eq a => Seq a -> Seq a -> Float
distanceSeq slm1 slm2 = d / ml
   where
      ml = realToFrac $ max (Seq.length slm1) (Seq.length slm2) 
      d = getSum $ fold $ seq.zipWith (\x y -> if x == y then Sum 1 else Sum 0) slm1 slm2
-}
{-type GeneralRadius = Float

generalizationPattern :: GeneralRadius -> HashSet (Seq a) -> (Seq a,HashSet (Seq a), HashSet (Seq a))
generalizationPattern gr hsslm = (gslm,shsseqLM,zhsslm)
   where
      (shsseqLM, zhsslm) = HSet.partition (\slm-> (distanceSeq slm gslm) > gr ) hsslm
      gslm = foldl1 (\ (d1,slm1) (d2,slm2) -> if d1 > d2 then (d1,slm1) else (d2,slm2)) ldslm
      ldslm = fmap (\slm1-> let
         ad = foldl1 (+) $ fmap (\slm2 -> distanceSeqLM slm1 slm2) hsslm
	 in (ad / (realToFrac $ Seq.length hsslm), slm1)
	 ) $ HSet.toList hsslm
-}
-- Pattern for pattern exist for reception, but not for liniar memorym because linear memory is uneq patern for eny reception
--
-- type SeqR i != SeqLM i
type SeqR i = Seq (HashSet (DendritPatern i, PointAndR i) )

readReception ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   WaveStep ->
   -- QueueWriteDP i ->
   SeqLM i ->
   [PointAndR i] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (SeqR i)
readReception ws seqLM lpr w = do
   quWdp <- newTQueueIO 
   quRdp <- newtQueueIO 
   mapM (\ dppr -> do 
      atomicaly $ writeTQueue quWdp (fst dppr)
      ) seqLM
   dendritWriteRead ws quWdp quRdp lpr w
   seqrdp <- fmap (foldl (\ b a -> b :>| (fold $ fmap HSet.singletone a)) Seq.empty) $ atomicaly $ flushTQueue quRdp 
   return seqrdp 

type Reception i = HashSet (DendritPatern i, PointAndR i) 

type ReceptionBind i = HashMap (HashSet (DendritPatern i, PointAndR i)) (DendritPatern i, PointAndR i, Int)

type ReceptionBind_A i = HashMap (HashSet (DendritPatern i, PointAndR i)) (Set Int)

indexedSeq i = Seq.iterateN i (+ 1) 0 

receptionBind_A ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   WaveStep ->
   -- QueueWriteDP i ->
   SeqLM i ->
   [Reception i] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (ReceptionBind_A i)
receptionBind_A ws seqLM lr w =
   quWdp <- newTQueueIO 
   quRdp <- newtQueueIO
   fmap foldl $ mapM (\hsdppr->do
      atomicaly $ writeTQueue quWdp $ fmap (fst) $ HSet.toLisst hsdppr
      seqBool <- dendritReactLinearMemory seqLM ws quWdp quRdp w
      let sib = Seq.filter (\(i,b)->b) $ Seq.zip (indexedSeq $ Seq.length seqBool) seqBool
      return $ foldl (HMap.unionWith (<>)) (HMap.epmty) $ fmap (\(i,_)-> HMap.singletone hsdppr (Set.singletone i)) sib
      ) lr

type FrecuencyReception i = Map Int [(HashSet (DendritPatern i, PointAndR i),Set Int)] -- List is Not emty and only one ???????
type IndexReception i = Map Int [(HashSet (DendritPatern i, PointAndR i))]

indexReception :: ReceptionBind_A i -> IndexReception i 
indexReception rba = foldl (Map.unionWith (<>)) (Map.empty) $ 
   mapWithKey (\ k li -> foldl (Map.unionWith (<>)) (Map.empty) $ fmap (\i-> Map.singletone i [k]) li) rba

frecuencyReception :: ReceptionBind_A i -> FrecuencyReception i 
frecuencyReception rba = foldl (Map.unionWith (<>)) (Map.empty) $ 
   mapWithKey (\ k li -> Map.singletone (P.length li) [(k,li)]) rba

type DivFrecuency = Float -- Int -- Float

frecuencyPartition :: DivFrecuency -> FrecuencyReception i -> (FrecuencyReception i, FrecuencyReception i)
frecuencyPartition df fr = maybe (Map.empty,Map.empty) id $ mapM (\(k,lhsdpprli) -> let 
   hk = round $ (realToFrac k) / df
   in Map.partition (\x-> x >= df) fr
   ) mmf
   where
      mmf = lookupMax fr

--type PatternR = Int

type PatternSeq i = Seq 

generationPatternReception :: DivFrecuency -> PatternRadius -> ReceptionBind_A i -> HeshSet (SeqR i)
generationPatternReception df pr rb = fold $ fmap (HSet.singletone) $ fold $ fmap (\ lhsdppri -> join $ fmap (\ (hs,si) -> let
      li = fold $ fmap (: []) si
      in fmap (\ i -> let
            lhs = fmap (\ j -> maybe HSet.empty id $ fmap (\ lhs -> P.head lhs) $ Map.lookup j ir
	    in foldl (\ s hs -> s :>| hs) Seq.empty lhs
	    ) [x | x <- (i-pr,i-pr+1 .. i+pr) ]
	 ) li
      ) lhsdppri
   ) fr
   where
      (frU,_) = frecuencyPartition df fr
      fr = frecuencyReception rb
      ir = indexReception rb
{-
distanceSeqR :: SeqR i -> SeqR i -> FLoat
distanceSeqR slm1 slm2 = d / ml  -- COPYPASTA !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! distanceSeqLM
   where
      ml = realToFrac $ max (Seq.length slm1) (Seq.length slm2) 
      d = getSum $ fold $ seq.zipWith (\x y -> if x == y then Sum 1 else Sum 0) slm1 slm2
-}
-- generalizationPatternReception :: [SeqR i] -> (SeqR i, HashSet (SeqR i))
-- generalizationPatternReception lsri = 

type MemoryPattern i = HashMap (SeqR i) (HashSet (SeqR i))

dendritPatternMemory ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   TVar (MemoryPattern i) ->
   WaveStep ->
   SeqR i ->
   HashSet (SeqR i) ->
   -- QueueReadDP i ->
   QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
dendritPatternMemory tvsDP s srg hss quPLM w =
   lPLM <- atomicaly $ flushTQueue quPLM
   -- lldp <- atomicaly $ flushTQueue quW
   quWdp <- newTQueueIO 
   quRdp <- newtQueueIO
   let (pM : lMN) = lPLM
   pG <- f quWdp quRdp srg pM w
   shshdp <- fmap (fold . fmap HSet.singeltone) $ mapM (\ (plm,ldp) -> do
      f quWdp quRdp ldp plm w
      ) $ zip lMN $ HSet.toList $ (fmap . fmap) fst hss
   atomicaly $ modifyTVar tvsDP (\ mp -> 
      HMap.alter (\mhss -> (do
         hss <- mhss
	 return $ union hss shshdp
	 ) <|> (return shshdp)
	 ) pg mp
      )
   where
      f quWdp quRdp ldp plm w = do 
         shdp <- foldl (\ s dp -> do
	    atomivaly $ do
               writeTQueue quWdp $ HSet.toList dp
	    dendritWriteRead s quWdp quRdp [plm] w
atomicaly $ do
               lrdp <- flushTQueue quRdp
               return $ s :>| (head lrdp) -- plm
	    ) (Seq.empty) ldp
	 return shdp

dendritReactSeqR ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   SeqR i -> -- [SeqR i] -> -- TVar (SeqLM i) ->
   WaveStep ->
   QueueWriteDP i ->
   QueueReadDP i ->
   -- QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (Seq Bool)
dendritReactSeqR lsdpp s quW quR w =
   -- sdpp <- readTVarIO tvsDP 
   let lpr = fold $ fmap ( (: []) . HSet.toList . fmap snd ) sdpp  -- join $ (fmap . fmap) ( (: []) . HSet.toList . fmap snd ) lsdpp
   dendritWriteRead s quW quR lpr w
   seqrdp <- fmap (foldl (\ b a -> b :>| (fold $ fmap HSet.singletone a)) Seq.empty) $ atomicaly $ flushTQueue quRdp
   return Seq.zipWith (\ (dp,pr) hsDp -> HSet.member (dp,pr) hsDp) sdpp seqrdp

dendritReactSeqRHM ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   TVar (HashMap (SeqR i) (Seq Bool)) -> -- [SeqR i] -> -- TVar (SeqLM i) ->
   WaveStep ->
   QueueWriteDP i ->
   QueueReadDP i ->
   -- QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (Int)
dendritReactSeqRHM tvhmSiSb ws quWdp quRdp w =
   hmSiSb <- readTVarIO tvhmSiSb 
   let lSR = HMap.keys hmSiSb
   let maxL = getMax $ fold $ fmap (Max . Seq.length) lSR
   lldp <- atomicaly $ flushTQueue quWdp
   let lengthLDP = P.length lldp
   mapM (\(i,ldp)-> do
      hmSiSbN <- readTVarIO tvhmSiSb 
      let lSRK = HMap.keys hmSiSbN
      let lhsPP = catMaybes $ fmap (\s-> lookup i s >>= (\pp-> return (pp,s))) lSRK
      -- let hsPP = fold lhsPP
      atomicaly $ writeTQueue quWdp [ldp]
      dendritWriteRead s quWdp quRdp (join $ fmap (HSet.toList) lhsPP) w
      ldpO <- fmap head $ atomicaly $ flushTQueue quRdp
      mapM (\ dprp -> mapM (\ (hsPP,s) -> do
            if HSet.member dprp hsPP 
	       then do
	          modifyTVar tvhmSiSb (adjust (:>| True) s)
	       else return ()
	    ) lhsPP
         ) ldpO
      modifyTVar tvhmSiSb (fmap (\s-> if Seq.lendth s > i then s else s :>| False))  
      ) $ P.zip [0 .. maxL] lldp
   return lengthLDP
   
minDistancePattern :: HashMap (SeqR i) (Seq Bool) -> (SeqR i, Float)
minDistancePattern hm = HMap.foldlWithKey (\ k v (s,maxS) -> if v >= maxS then (k,v) else (s,msxS)) (Empty, 0) $ 
   fmap (\ sb1 -> getMax $ fold $ fmap (\sb2 -> let 
      d = distanceSeq sb1 sb2
      in Max d
      ) hm ) hm 
-- distanceSeq
lengthTQueue qu = atomicaly $ do
   la <- flushTQueue qu
   mapM (\a-> writeTQueue qu a) la -- reverse ????????????????????? 
   return $ P.lenght la

dendritReactPatternMemory ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   MemoryPattern i -> -- TVar (SeqLM i) ->
   WaveStep ->
   QueueWriteDP i ->
   QueueReadDP i ->
   -- QueuePLM i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (Int,SeqR i, Float, SeqR i, Float)
dendritReactPatternMemory mp ws quWdp quRdp w =
   -- lQuRdp <- lengthTQueue quRdp
   la <- atomicaly $ flushTQueue qu 
   mapM (\a-> atomicaly $ writeTQueue qu a) la
   let lK = HMap.keys mp
   let hmKS = fmap (\ k -> HMap.singletone k (Seq.empty)) lK
   tvhmKS <- newTVarIO hmKS
   ldp <- dendritReactSeqRHM tvhmKS ws quWdp quRdp w
   hmKSN <- readTVarIO tbhmKS
   let (minPatt,t1) = minDistancePattern hmKSN
   mapM (\a-> atomicaly $ writeTQueue qu a) la -- Reapit block cod !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
   let hsSeqIn = HSet.insert minPatt (mp HMap.! minPatt) 
   let hmKS2 = fmap (\ k -> HMap.singletone k (Seq.empty)) $ HSet.toList hsSeqIn
   atomicaly $ writeTVar tvhmKS hmKS2
   dendritReactSeqRHM tvhmKS ws quWdp quRdp w
   hmKSN2 <- readTVarIO tbhmKS
   let (minPatt2,t2) = minDistancePattern hmKSN2
   return (ldp,minPatt2,t2,minPatt,t1)

data DendritState 
   = LinearMemory
   | PatternMemory

type FlagP2P1 = Bool

type FlagSuggestion = Bool

data DendritIO i a = DendritIO 
   { receptionIO :: IO (a, MemoryPattern i)
   , reaction :: (Int,SeqR i, Float, SeqR i, Float) -> FlagP2P1 -> FlagSuggestion -> a -> IO ()
   , bindDendrit :: HashMap a (Reception i)
   , reBindDendrit :: HashMap (Reception i) a 
   , localMemPattern :: TVar (MemoryPattern i) 
   , localMemLinear :: TVar (SeqLM i)
   , freeLinearPoint :: QueuePLM i
   , maxMemLinear :: Int
   , lastReaction :: TVar (Int,SeqR i, Float, SeqR i, Float)
   , receptionInterval :: TVar (Seq a)
   , receptionIntervalMax :: Int
   , stateDendrit :: TVar DendritState
   , dendritWaveStep :: WaveStep
   , generatorDivF :: DivFrecuency 
   , generatorPatternR :: PatternRadius
   , generalizationRadius :: GeneralRadius
   }

generalizationCycle :: :
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   HeshSet (SeqR i) ->
   DendritIO i b ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () 
generalizationCycle hsR dio w = do
   let (gPattern,inPattern,outPattern) = generalizationPattern (generalizationRadius dio) hsR
   dendritPatternMemory 
      (localMemPattern dio) (dendritWaveStep dio) gPattern inPattern (freeLinearPoint dio) w
   if HSet.null inPattern
      then do
        dendritPatternMemory 
           (localMemPattern dio) (dendritWaveStep dio) Seq.empty outPattern (freeLinearPoint dio) w
      else do
         dendritPatternMemory 
            (localMemPattern dio) (dendritWaveStep dio) gPattern inPattern (freeLinearPoint dio) w
	 generalizationCycle outPattern dio w

ioPatternMemory :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   MemoryPattern i ->
   DendritIO i b ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () 
ioPatternMemory lMP dio w = do
   -- IO Pattern Memory
   ri <- readTVarIO $ receptionInterval dio
   let rin = f1 dio $ ri :>| b
   atomicaly $ writeTVar (receptionInterval dio) rin
   quW <- newTQueueIO
   quR <- newTQueueIO
   mapM (\a-> atomicaly $ writeTQueue quW a) rin
   lp2p1@(lW,p2,d2,p1,d1) <- dendritReactPatternMemory 
      lMP (dendritWaveStep dio) quW quR w
   lastR@(lWl,p2l,d2l,p1l,d1l) <- readTVarIO $ lastReaction dio
   atomicaly $ writeTVar (lastReaction dio) lp2p1
   let mb1 = (\hs-> HMap.lookup hs (reBindDendrit dio) ) =<< (Seq.lookup (lWl + 1) p1l)   
   let mb2 = (\hs-> HMap.lookup hs (reBindDendrit dio) ) =<< (Seq.lookup (lWl + 1) p2l)
   let mbn = (\hs-> HMap.lookup hs (reBindDendrit dio) ) =<< (Seq.lookup (lW + 1) p2) 
   if and [(mb1 == mb) || (mb2 == mb), mb1 /= Nothing, mb2 /= Nothing]
      then do
         mapM (\bn-> (reaction dio) lastR (mb2 == mb) True bn) mbn
      else do
	 mapM (\bn-> (reaction dio) lastR (mb2 == mb) Flase bn) mbn 
   where
      f1 dio ri@(_ :<| s) = if Seq.length rin1 > (receptionIntervalMax dio) 
         then return s
	 else return ri
      f1 _ ri = ri
   

dendritIO ::
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , RandomGen g
   , Random i
   , CxtAxon i w a g
   ) =>
   DendritIO i b ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO () 
dendritIO dio w = do
   (b,mpS) <- receptionIO dio
   dst <- readTVarIO $ stateDendrit dio
   let bdAR = bindDendrit dio
   let mrecIn = HMap.lookup b bdAR 
   case dst of
      LinearMemory -> do
         mapM (\recIn-< do
	    quWdp <- newTQueueIO 
	    atomicaly $ writeTQueue quWdp $ fmap fst $ HSet.toList recIn
	    dendritLinearMemory 
	       (localMemLinear dio) (dendritWaveStep dio) quWdp (freeLinearPoint dio) w
	    seqLM <- readTVarIO $ localMemLinear dio 
	    if Seq.length seqLM > (maxMemLinear dio)
	       then 
	          atolicaly $ writeTVar (stateDendrit dio) PatternMemory
	    ) mrecIn
      PatternMemory -> do
         lMP <- readTVarIO (localMemPattern dio)
         if (HMap.size lMP) == 0 
	    then do
	       -- init Memory Pattern
	       let bDR = bindDendrit dio
	       let lR = HMap.elems
	       lML <- readTVarIO (localMemLinear dio)
	       bA <- receptionBind_A (dendritWaveStep dio) lML lR w
	       let hsGPR = generationPatternReception (generatorDivF dio) (generatorPatternR dio) ba
               generalizationCycle hsGPR dio w
	       -- return point in Seq Linear Memory
	       seqLM <- readTVarIO $ localMemLinear dio
	       atomicaly $ writeTVar (localMemLinear dio) Seq.empty
               let seqRP = fmap snd seqLM
	       mapM (\rp-> atomicaly $ writeTQueue (freeLinearPoint dio) rp) seqRP
            else do
	       if (HMap.size mpS) == 0
	          then ioPatternMemory lMP dio w
		  else ioPatternMemory mpS dio w
   where
      f1 dio ri@(_ :<| s) = if Seq.length rin1 > (receptionIntervalMax dio) 
         then return s
	 else return ri
      f1 _ ri = ri


