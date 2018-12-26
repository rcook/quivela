-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.Util
  ( foreachM
  , heredoc
  , readFileCompileTime
  , uncurry3
  ) where

import qualified Control.Monad as Monad
import qualified Data.List as L
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH (Exp, Q)
import qualified Language.Haskell.TH.Quote as TH
import qualified Language.Haskell.TH.Syntax as TH
import Quivela.Prelude
import qualified System.Directory as Directory
import qualified System.FilePath as FilePath
import System.FilePath ((</>))
import qualified System.IO as IO

heredocExpr :: String -> Q Exp
heredocExpr s = TH.litE . TH.StringL $ s

-- | A quasi-quoter allowing for multi-line string literals
heredoc :: TH.QuasiQuoter
heredoc = TH.QuasiQuoter heredocExpr invalidUse invalidUse invalidUse
  where
    invalidUse _ = error "Invalid context for heredoc quasi-quotation"

-- | Read file contents at compile time and insert them as a literal expression.
-- the file path is expected to be relative to the current file or an absolute
-- path.
readFileCompileTime :: FilePath -> Q Exp
readFileCompileTime inFile = do
  curFile <- TH.loc_filename <$> TH.location
  pwd <- TH.runIO Directory.getCurrentDirectory
  let baseDir = FilePath.takeDirectory $ pwd </> curFile
      file = baseDir </> inFile
  exists <- TH.runIO $ Directory.doesFileExist file
  Monad.unless exists $
    TH.reportError ("readFileCompileTime: No such file: " ++ file)
  TH.addDependentFile file
  TH.runIO (IO.readFile file) >>= heredocExpr

-- | Take a list of monadic actions producing lists and map another monadic function over
-- the list and concatenate all results. This is basically a monadic version of the
-- bind operator in the list monad.
foreachM :: (Monad m) => m [a] -> (a -> m [b]) -> m [b]
foreachM s act = do
  xs <- s
  ys <- Monad.mapM act xs
  return $ L.concat ys

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c
