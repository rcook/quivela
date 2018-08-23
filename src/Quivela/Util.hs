{-# LANGUAGE TemplateHaskell #-}
module Quivela.Util (heredoc) where

import Language.Haskell.TH as TH hiding (Type)
import Language.Haskell.TH.Quote

heredocExpr :: String -> Q Exp
heredocExpr s = litE . TH.StringL $ s

-- | A quasi-quoter allowing for multi-line string literals
heredoc :: QuasiQuoter
heredoc = QuasiQuoter heredocExpr invalidUse invalidUse invalidUse
  where invalidUse _ = error "Invalid context for heredoc quasi-quotation"
