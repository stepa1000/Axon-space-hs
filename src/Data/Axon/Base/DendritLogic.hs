{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Data.Axon.Base.DendritLogic where

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
import Control.Monad.Logic

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
   lift $ mapConcurrently (\dp-> atomicaly $ writeDendritPatern dp w) $ fmap fst ldp
   ldp <- lift $ updateDedritSpace ws (fmap snd ldp) $ \ wn -> do
      mapM (\lpr -> do
         mapConcurrently (\(p,r)-> do
            dpn <- atomicaly $ readDendritPatern p r
            return (HSet.singletone dpn,(p,r))
	    ) lpr 
         ) llpr
   f $ fmap (return . join) ldp
   where
      f (x:xs) = x `interleave` (f xs)
      f (x:[]) = x
      f [] = empty

class Memorize i a where
   lPattern :: Lens' a (Seq (HashSet (DendritPatern i)))
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
	 let mhs = Seq.lookup seqP (llp + 1)
	 maybes (do
	    writeArray arr p $ set lPattern (Seq.update (HSet.singletone dp) seqP) a 
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
   LogicT IO Bool -- (HashSet (DendritPatern i), PointAndR i)
memorizeSeq ws tvAM tvSM quPAR ldp w = (do
   lam <- lift $ do
      lam <- readTVarIO tvAM
      if P.null lam
         then do
	    nam <- atomicaly $ readTQueue quPAR
	    atomicaly $ writeTVar tvAM [nam]
	    return [nam]
	 else return lam
   updateDendritLogic ws lam ldp w) >>- (\ dppr -> do
   eEC<- memorizeRightDL dppr w
   case eEC of
      (Left pr) -> do
         lift $ do
	    seqM <- readTVarIO tvSM
	    atomicaly $ writeTVar tvSM (seqM :>| pr)
            atomicaly $ modifyTVar tvAM (delete pr)
	    return True
      (Right pr) -> return False
   )

checkMemorize ::  
   ( Comonad w-- CxtAxon i w a g
   , Ix i
   , Num i
   , CxtAxon i w a g 
   , Memorize i a
   ) =>
   LogicT IO Bool ->
   LogicT IO (Either String Int)
checkMemorize ltiob = ifte (once $
   (many ltiob) >>- (\lb-> do
   return $ Right $ getSum $ fold $ fmap (\b->if b then Sum 1 else Sum 0) lb
   )) 
   return
   (return $ Left "LogicT hav not elements")

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
memorizeSeqCheck ws tvAM tvSM quPAR ldp w = checkMemorize $ memorizeSeq ws tvAM tvSM quPAR ldp w 
   

