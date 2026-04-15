{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.DendritLogic where

import Prelude as P

import Control.Monad
import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM.TArray
import Control.Concurrent.STM.TQueue
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
import Data.List as List
import Data.Maybe
import Control.Concurrent.Async
import Data.Traversable
import Data.Foldable as Fold
import Data.Proxy
import Data.UUID
import Data.Sequence as Seq
import Control.Monad.Logic
import Control.Applicative as Alt
import Data.Monoid

import Data.Axon.Base.Axon
import Data.Axon.Base.Types

updateDendritLogic :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   ) => 
   WaveStep ->
   [PointAndR i] ->
   [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (DendritPatern i, PointAndR i) -- (HashSet (DendritPatern i), PointAndR i)
updateDendritLogic ws lpr ldp w = do
   lift $ mapConcurrently (\dp-> atomically $ writeDendritPatern dp w) $ fmap fst ldp
   ldp <- lift $ updateDedritSpace ws (fmap snd ldp) (\ wn -> do
      mapConcurrently (\(p,r)-> do
         dpn <- atomically $ readDendritPatern p r
         return (HSet.singleton dpn,(p,r))
         ) lpr 
      ) w
   f $ fmap (return . join) ldp
   where
      f (x:xs) = x `interleave` (f xs)
      f (x:[]) = x
      f [] = Alt.empty

class Memorize i a where
   lPattern :: Lens' a (Seq (HashSet (DendritPatern i))) -- Linera !?!?!?!?!?!?!??!?!?!?
   lPatternMax :: Lens' a Int
   lLenghtPattern :: Lens' a Int

memorizeRight ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   (DendritPatern i, PointAndR i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO (Either (PointAndR i) (PointAndR i)) -- LogicT IO (Either (PointAndR i) (PointAndR i))
memorizeRight dppr@(dp,(p,r)) w = do
   let arr = coask w
   a <- readArray arr p
   let llp = a^.lLenghtPattern
   let lpm = a^.lPatternMax
   if llp >= lpm 
      then return $ Left (p,r)
      else do
         let seqP = a^.lPattern
	 let mhs = Seq.lookup (llp + 1) seqP
	 maybes (do
	    writeArray arr p $ set lPattern (Seq.update (HSet.singleton dp) seqP) a 
	    ) (\hs-> do
            writeArray arr p $ set lPattern (Seq.update (HSet.insert dp hs) seqP) a
	    ) mhs
         return $ Right (p,r)
   
memorizeRightList ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   [(DendritPatern i, PointAndR i)] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(Either (PointAndR i) (PointAndR i))] -- 
memorizeRightList ldp w = mapM (\ dppr -> memorizeRight dppr w) ldp 

memorizeRightDL ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   (DendritPatern i, PointAndR i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (Either (PointAndR i) (PointAndR i)) -- 
memorizeRightDL ldp w = do
   lift $ memorizeRight ldp w 

type ActiveMemorize i = [PointAndR i]

type SeqMemorize i = Seq (PointAndR i)

type TQueuePointAndR i = TQueue (PointAndR i)

memorizeSeq ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   WaveStep ->
   TVar (ActiveMemorize i) ->
   TVar (SeqMemorize i) ->
   TQueuePointAndR i ->
   [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (Bool, (i,i)) -- (HashSet (DendritPatern i), PointAndR i)
memorizeSeq ws tvAM tvSM quPAR ldp w = (do
   lam <- lift $ do
      lam <- readTVarIO tvAM
      if P.null lam
         then do
	    nam <- atomicaly $ readTQueue quPAR
	    atomically $ writeTVar tvAM [nam]
	    return [nam]
	 else return lam
   updateDendritLogic ws lam ldp w) >>- (\ dppr -> do
   eEC<- memorizeRightDL dppr w
   case eEC of
      (Left pr@(p,_)) -> do
         lift $ do
	    seqM <- readTVarIO tvSM
	    atomically $ writeTVar tvSM (seqM :|> pr)
            atomically $ modifyTVar tvAM (List.delete pr)
	    return (True,p)
      (Right (p,_)) -> do
         -- memoryNextSeq p w
	 return (False,p)
   )

checkMemorize ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   LogicT IO (Bool,(i,i)) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (Either String Int)
checkMemorize ltiob w = ifte (
   (many ltiob) >>- (\lb-> once $ do
   mapM (\p-> lift $ memoryNextSeq p w) $ fmap snd lb
   return $ Right $ getSum $ Fold.fold $ fmap (\b->if b then Sum 1 else Sum 0) $ fmap fst lb
   )) 
   return
   (return $ Left "LogicT hav not elements")

memoryNextSeq ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   (i,i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
memoryNextSeq p w = do
   let arr = coask w
   a <- readArray arr p
   let llp = a^.lLenghtPattern
   writeArray arr p $ set lLengthPattern (llp + 1) a

memorizeSeqCheck ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   WaveStep ->
   TVar (ActiveMemorize i) ->
   TVar (SeqMemorize i) ->
   TQueuePointAndR i ->
   [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (Either String Int) -- (HashSet (DendritPatern i), PointAndR i)
memorizeSeqCheck ws tvAM tvSM quPAR ldp w = do
   checkMemorize $ memorizeSeq ws tvAM tvSM quPAR ldp w 

forMemory ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   TVar (SeqMemorize i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [PointAndR i]
forMemory tvseqM w = do
   fmap (Fold.foldl (:) []) $ readTVarIO tvseqM 
   -- foldl1 (interleave) $ fmap return seqM
 
memoryReact ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   (DendritPatern i,PointAndR i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [Int]
memoryReact (dp,pr@(p,r)) w = do
   let arr = coask w
   a <- readArray arr p 
   let seqP = a^.lPattern
   let seqI = Seq.iterateN (Seq.length seqP) (+ 1) 0
   fmap Fold.fold $ mapM (\(hs,i) -> do
      if HSet.member dp hs 
         then return [i]
	 else return []
      ) $ Seq.zip seqP seqI

memoryReactDL ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   WaveStep ->
   TVar (SeqMemorize i) ->
   [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (DendritPatern i, PointAndR i, [Int])
memoryReactDL ws tvSM ldp w = (do
   lpr <- lift $ forMemory tvSM w
   updateDendritLogic ws lpr ldp w) >>- (\ dppr@(dp,pr) -> do
   li <- lift $ memoryReact dppr w
   if P.null li then Alt.empty
      else return (dp,pr,li) 
   )

type RadiusPattern = Int

type SeqPattern i = Seq (HashSet (DendritPatern i))

genPatternRadius ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   RadiusPattern ->
   (DendritPatern i, PointAndR i, [Int]) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(SeqPattern i, PointAndR i)]
genPatternRadius r (dp,pr@(p,ri),li) w = do
   let arr = coask w
   a <- readArray arr p 
   let seqP = a^.lPattern
   let seqI = Seq.iterateN (Seq.length seqP) (+ 1) 0
   let seqPI = Seq.zip seqP seqI
   fmap Fold.fold $ mapM (\i -> do 
      let seqPF = Seq.filter (\ (_,j) -> j > (i - r) && j < (i + r)) seqPI
      if Seq.null seqPF
         then return []
	 else return [(fmap . fmap) fst seqPF]
      ) li

genPatternString ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   (DendritPatern i, PointAndR i, [Int]) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(SeqPattern i, PointAndR i)]
genPatternString (dp,pr@(p,ri),li) w = do 
   let arr = coask w
   a <- readArray arr p 
   let seqP = a^.lPattern
   let seqI = Seq.iterateN (Seq.length seqP) (+ 1) 0
   let seqPI = Seq.zip seqP seqI
   let ls = List.sort li 
   fmap join $ mapM (\ (x,y) -> do
      let seqPF = Seq.filter (\ (_,j) -> j > x && j < y) seqPI
      if Seq.null seqPF
         then return []
	 else return [(fmap fst seqPF, pr)] 
      ) $ f ls
   where
      f (x:y:xs) = (x,y) : (f (y:xs))
      f _ = []

genAnyPatternsDL ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   RadiusPattern ->
   (DendritPatern i, PointAndR i, [Int]) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (SeqPattern i, PointAndR i)
genAnyPatternsDL rp dppri w = do
   lp <- lift $ do
      l1 <- genPatternRadius rp dppri w
      l2 <- genPatternString dppri w
      return $ l1 ++ l2
   Fold.foldl (\m sp -> interleave m (return sp)) Alt.empty lp

class MemoryPattern i a where
   lMemoryPattern :: Lens' a (HashSet (SeqPattern i))

addMemoryPattern ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   (SeqPattern i, PointAndR i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO ()
addMemoryPattern (sp,(p,r)) w = do
   let arr = coask w
   a <- readArray arr p 
   let lSeqP = a^.lMemoryPattern 
   writeArray arr p $ set lMemoryPattern (HSet.insert sp lSeqP) a

reactMemoryPattern ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   (DendritPatern i, PointAndR i) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(SeqPattern i, PointAndR i, [Int])]
reactMemoryPattern (dp,pr@(p,r)) w = do
   let arr = coask w
   a <- readArray arr p 
   let hsSeqP = a^.lMemoryPattern 
   mapM (\ seqP -> do
      let seqI = Seq.iterateN (Seq.length seqP) (+ 1) 0
      li <- fmap Fold.fold $ mapM (\(hs,i) -> do
         if HSet.member dp hs 
            then return [i]
	    else return []
         ) $ Seq.zip seqP seqI
      return (seqP,pr,li)
      ) $ HSet.toList hsSeqP

reactMemoryPatternSeq ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   Seq [(DendritPatern i, PointAndR i)] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(SeqPattern i, Float)]
reactMemoryPatternSeq seqDPPR w = do
   let arr = coask w
   let (((_,(p,_)):_) :<| _) = seqDPPR
   a <- readArray arr p 
   let hsSeqP = a^.lMemoryPattern 
   mapM (\ seqP -> do
      let seqP2 = fmap Fold.fold $ (fmap . fmap) (HSet.singleton fst) seqDPPR
      return (seqP, distanceSeq seqP seqP2) 
      ) $ HSet.toList hsSeqP

reactMemoryPatternDL ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   WaveStep ->
   [PointAndR i] ->
   [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (SeqPattern i, PointAndR i, [Int]) 
reactMemoryPatternDL ws lp lldp w = (do
   updateDendritLogic ws lp lldp w) >>- (\ dppr@(dp,pr) -> do
   li <- lift $ reactMemoryPattern dppr w
   if P.null li then Alt.empty
      else Fold.foldl (\m sp -> interleave m (return sp)) Alt.empty li
   )

class GeneralPattern i a where
   gPattern :: Lens' a (Maybe (Seq [DendritPatern i]))-- Prism' a (Seq [DendritPatern i])
   lPointIn :: Lens' a [PointAndR i]

reactGeneralPatternSeq ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   Seq [(DendritPatern i, PointAndR i)] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   IO [(SeqPattern i, Float)]
reactGeneralPatternSeq seqDPPR w = do
   let arr = coask w
   let (((_,(p,_)):_) :<| _) = seqDPPR
   a <- readArray arr p 
   let mSeqP = a^.gPattern 
   mapM (\ seqP -> do
      let seqP2 = fmap Fold.fold $ (fmap . fmap) (HSet.singleton fst) seqDPPR
      return (seqP, distanceSeq seqP seqP2) 
      ) mSeqP

generalizationMemoryPatternG ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   WaveStep ->
   [PointAndR i] -> 
   -- GeneralRadius ->
   Seq [DendritPatern i] ->
   -- HashSet (Seq [DendritPatern i]) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (PointAndR i) -- (HashSet (Seq [DendritPatern i])) 
generalizationMemoryPatternG ws pr hssdp w = (do
    -- let (seqG,inG,outG) = generalizationPattern gr hssdp
   updateDendritLogicSeq ws pr ((fmap . fmap) (\x->[x]) hssdp) w
   ) >>- (indexSort
   ) >>- (\ seqdppr -> do
   (b,a,prN@(p,_)) <- chackSeqPattern seqdppr
   if b then do
         writeArray arr p $ set gPattern (Just seqDP) a 
         return prN
      else Alt.empty
   )

indexSort ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   (Seq [(DendritPatern i, PointAndR i)]) ->
   LogicT IO (Seq [(DendritPatern i, PointAndR i)])
indexSort = (\ seqdppr -> do
   let lSeqdppr = f seqdppr
   Fold.foldl (\m sp -> interleave m (return sp)) Alt.empty lSeqdppr
   )
   where
      f (ldppr :<| seq) = 
         fmap (\x@(dp,(p,r))-> x :<| 
	    (fmap 
	       (P.filter (\(sp2,(p2,r2))-> p == p2)) 
	       seq) 
	    ) ldppr
      f _ = Seq.Empty

   
chackSeqPattern ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   (Seq [(DendritPatern i, PointAndR i)]) ->
   LogicT IO (Bool,a,PointAndR i)
chackSeqPattern = (\ seqdppr -> do
   when ((Seq.length seqdppr) <= 0) Alt.empty
   let (((dp,(p,r)):_) :<| _) = seqdppr
   let seqDP = fmap Fold.fold $ (fmap . fmap) (HSet.singleton . fst) seqdppr
   lift $ do
      let arr = coask w
      a <- readArray arr p 
      let lseqP = a^.lMemoryPattern 
      let b = or $ fmap (== seqDP) lseqP
      return (b,a,(p,r))
   ) 


generalizationMemoryPatternInG ::   
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   WaveStep ->
   [PointAndR i] -> 
   PointAndR i ->
   -- GeneralRadius ->
   -- Seq [DendritPatern i] ->
   HashSet (Seq [DendritPatern i]) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (PointAndR i) -- (HashSet (Seq [DendritPatern i])) 
generalizationMemoryPatternInG ws pr prG@(pG,_) hssdp w = (do
   mapM (\ sdp -> do
      updateDendritLogicSeq ws pr ((fmap . fmap) (\x->[x]) sdp) w
      ) hssdp 
   ) >>- indexSort 
   >>- (\ seqdppr -> do
   (b,a,prN@(p,_)) <- chackSeqPattern seqdppr
   if b then do
         writeArray arr pG $ over lPointIn (prN :) a 
         return prN
      else Alt.empty
   )

generalizationMemoryPatternUpdate ::    
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) => 
   WaveStep ->
   [PointAndR i] -> 
   GeneralRadius ->
   -- Seq [DendritPatern i] ->
   HashSet (Seq [DendritPatern i]) ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (PointAndR i)
generalizationMemoryPatternUpdate ws pr gr hssdp w = do
   let (seqG,inG,outG) = generalizationPattern gr hssdp 
   prG <- generalizationMemoryPatternG ws pr prG seqG w
   prInG <- one $ many $ generalizationMemoryPatternInOutG ws pr prG inG w
   if P.null prInG || P.null outG
      then return prG
      else interleave (return prG) (generalizationMemoryPatternUpdate outG)

updateDendritLogicSeq :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   ) => 
   WaveStep ->
   [PointAndR i] ->
   Seq [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (Seq [(DendritPatern i, PointAndR i)]) -- (HashSet (DendritPatern i), PointAndR i)
updateDendritLogicSeq ws lpr sldp w = do
   foldlM (\ seqN lldp -> do
      ldp <- many $ updateDendritLogic ws lpr lldp w 
      return $ seqN :>| ldp
      ) Seq.empty sldp

seqPatternToSeq :: SeqPattern i -> Seq [[(DendritPatern i,(i,i))]] 
seqPatternToSeq sp = fmap (fmap (\x-> [(x,midleDP x)]) . HSet.toList)sp

updateDendritLogicSeqPattern :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   ) => 
   WaveStep ->
   [PointAndR i] ->
   SeqPattern i ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (Seq [(DendritPatern i, PointAndR i)]) 
updateDendritLogicSeqPattern ws lpr sldp w = updateDendritLogicSeq ws lpr (seqPatternToSeq sldp) w 

type TVarGPointAndR i = TVar [PointAndR i]

updateDendritLogicSeqGeneral :: 
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   ) => 
   WaveStep ->
   TVarGPointAndR i ->
   -- [PointAndR i] ->
   Seq [[(DendritPatern i,(i,i))]] ->
   W.AdjointT 
      (AdjArrayL (i,i) a)
      (AdjArrayR (i,i) a)
      w
      b ->
   LogicT IO (Seq [(DendritPatern i, PointAndR i)]) -- (HashSet (DendritPatern i), PointAndR i)
updateDendritLogicSeqGeneral ws lpr sldp w = undefined -- do
   
