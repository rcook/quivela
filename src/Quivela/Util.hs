{-# LANGUAGE TemplateHaskell #-}
module Quivela.Util (heredoc, readFileCompileTime) where

import Control.Monad
import Language.Haskell.TH as TH hiding (Type)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import System.FilePath
import System.Directory

heredocExpr :: String -> Q Exp
heredocExpr s = litE . TH.StringL $ s

-- | A quasi-quoter allowing for multi-line string literals
heredoc :: QuasiQuoter
heredoc = QuasiQuoter heredocExpr invalidUse invalidUse invalidUse
  where invalidUse _ = error "Invalid context for heredoc quasi-quotation"

-- | Read file contents at compile time and insert them as a literal expression.
-- the file path is expected to be relative to the current file or an absolute
-- path.
readFileCompileTime :: FilePath -> Q Exp
readFileCompileTime inFile = do
  curFile <- loc_filename <$> location
  pwd <- runIO getCurrentDirectory
  let baseDir = takeDirectory $ pwd </> curFile
      file = baseDir </> inFile
  exists <- runIO $ doesFileExist file
  unless exists $
    reportError ("readFileCompileTime: No such file: " ++ file)
  addDependentFile file
  heredocExpr =<< runIO (readFile file)
