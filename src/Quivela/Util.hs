{-# LANGUAGE TemplateHaskell #-}

module Quivela.Util
  ( heredoc
  , readFileCompileTime
  ) where

import qualified Control.Monad as M
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
