{-# LANGUAGE TemplateHaskell #-}
module Quivela.Util (heredoc, readFileCompileTime) where

import Language.Haskell.TH as TH hiding (Type)
import Language.Haskell.TH.Quote

heredocExpr :: String -> Q Exp
heredocExpr s = litE . TH.StringL $ s

-- | A quasi-quoter allowing for multi-line string literals
heredoc :: QuasiQuoter
heredoc = QuasiQuoter heredocExpr invalidUse invalidUse invalidUse
  where invalidUse _ = error "Invalid context for heredoc quasi-quotation"

-- | Read file contents at compile time and insert them as a literal expression.
readFileCompileTime :: FilePath -> Q Exp
readFileCompileTime s = heredocExpr =<< runIO (readFile s)
