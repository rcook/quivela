-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
module Quivela.Prelude
  ( Applicative
  , Bool(False, True)
  , Char
  , Data
  , Double
  , Either(Left, Right)
  , Eq
  , FilePath
  , Foldable
  , Functor
  , Generic
  , IO
  , Int
  , Integer
  , Map
  , Maybe(Just, Nothing)
  , Monad
  , Monoid
  , Num
  , Ord
  , Semigroup
  , Serialize
  , Set
  , Show
  , String
  , Typeable
  , ($)
  , (&)
  , (&&)
  , (+)
  , (++)
  , (-)
  , (*)
  , (.)
  , (/=)
  , (<$>)
  , (<)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (>>=)
  , (||)
  , (<>)
  , const
  , div
  , error
  , flip
  , fmap
  , foldM
  , foldMap
  , fromInteger
  , fromIntegral
  , fst
  , id
  , map
  , mapM
  , mapM_
  , mempty
  , not
  , otherwise
  , printf
  , pure
  , putStrLn
  , return
  , show
  , snd
  , uncurry
  , undefined
  , writeFile
  ) where

import Control.Monad (foldM)
import Data.Data (Data)
import Data.Function ((&))
import Data.Map (Map)
import Data.Serialize (Serialize)
import Data.Set (Set)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Prelude
import Text.Printf(printf)
