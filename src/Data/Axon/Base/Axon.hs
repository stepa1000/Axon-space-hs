module Data.Axon.Base.Axon where

import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM.TArray
import Control.Core.Composition
import Control.Base.Comonad

-- Array

type AdjArrayL i a = Env (TArray i a)

type AdjArrayR i a = Reader (TArray i a)


