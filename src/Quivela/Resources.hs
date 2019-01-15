-- Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.Resources
  ( quivelaSmt2Content
  , quivelaSmt2Path
  ) where

import Data.FileEmbed (embedStringFile, makeRelativeToProject)
import Language.Haskell.TH (Exp, Q)
import Quivela.Prelude

-- | Fully qualified path to quivela.smt2
quivelaSmt2Path :: Q Exp -- ^ expression
quivelaSmt2Path = do
  fullPath <- makeRelativeToProject "src/Quivela/quivela.smt2"
  [|fullPath|]

-- | Embedded copy of quivela.smt2
quivelaSmt2Content :: String -- ^ content
quivelaSmt2Content = $(embedStringFile "src/Quivela/quivela.smt2")
