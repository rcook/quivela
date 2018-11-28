-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.Util
  ( debug
  , foreachM
  , heredoc
  , readFileCompileTime
  , uncurry3
  ) where

import qualified Control.Monad as M
import qualified Control.Monad.RWS.Strict as R
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as Q
import qualified Language.Haskell.TH.Syntax as S
import qualified System.Directory as D
import qualified System.FilePath as FilePath
import System.FilePath ((</>))

heredocExpr :: String -> TH.Q TH.Exp
heredocExpr s = TH.litE . TH.StringL $ s

-- | A quasi-quoter allowing for multi-line string literals
heredoc :: Q.QuasiQuoter
heredoc = Q.QuasiQuoter heredocExpr invalidUse invalidUse invalidUse
  where
    invalidUse _ = error "Invalid context for heredoc quasi-quotation"

-- | Read file contents at compile time and insert them as a literal expression.
-- the file path is expected to be relative to the current file or an absolute
-- path.
readFileCompileTime :: FilePath -> TH.Q TH.Exp
readFileCompileTime inFile = do
  curFile <- S.loc_filename <$> S.location
  pwd <- TH.runIO D.getCurrentDirectory
  let baseDir = FilePath.takeDirectory $ pwd </> curFile
      file = baseDir </> inFile
  exists <- TH.runIO $ D.doesFileExist file
  M.unless exists $
    TH.reportError ("readFileCompileTime: No such file: " ++ file)
  S.addDependentFile file
  heredocExpr =<< TH.runIO (readFile file)

-- | Print out debugging information.
debug :: (R.MonadIO m) => String -> m ()
debug = R.liftIO . putStrLn -- TODO: move this to a utility module or so

-- | Take a list of monadic actions producing lists and map another monadic function over
-- the list and concatenate all results. This is basically a monadic version of the
-- bind operator in the list monad.
foreachM :: (Monad m) => m [a] -> (a -> m [b]) -> m [b]
foreachM s act = do
  xs <- s
  ys <- mapM act xs
  return $ concat ys

-- | Uncurry a three-argument function (useful for partial application)
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c
