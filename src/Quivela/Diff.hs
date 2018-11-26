-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
module Quivela.Diff
  ( applyDiffs
  ) where

import Control.Lens ((^.), iso, over)
import qualified Quivela.Language as L
import Quivela.Language (Diff, Expr, Field, Var)

seqToList L.ENop = []
seqToList (L.ESeq e1 e2) = e1 : seqToList e2
seqToList _ = error "Invalid argument to seqToList"

replaceMethod :: Expr -> Expr -> Expr
replaceMethod emtd ebody
  | any
     (\e ->
        case e of
          mtd'@(L.EMethod {}) -> mtd' ^. L.emethodName == emtd ^. L.emethodName
          _ -> False)
     bodyExprs = foldr L.ESeq L.ENop $ map replace bodyExprs
  where
    replace mtd'@(L.EMethod {})
      | mtd' ^. L.emethodName == emtd ^. L.emethodName = emtd
      | otherwise = mtd'
    replace e = e
    bodyExprs = seqToList ebody
replaceMethod emtd ebody = foldr L.ESeq L.ENop (seqToList ebody ++ [emtd])

replaceField :: Field -> [Field] -> [Field]
replaceField newField oldFields
  | any
     (\oldField -> oldField ^. L.fieldName == newField ^. L.fieldName)
     oldFields = map replace oldFields
  where
    replace oldField
      | oldField ^. L.fieldName == newField ^. L.fieldName = newField
      | otherwise = oldField
replaceField newField oldFields = oldFields ++ [newField]

deleteMethod :: Var -> Expr -> Expr
deleteMethod mtdName body =
  over
    (iso seqToList (foldr L.ESeq L.ENop))
    (filter
       (\e ->
          case e of
            oldMtd@L.EMethod {} -> oldMtd ^. L.emethodName /= mtdName
            _ -> True))
    body

applyDiff :: Diff -> Expr -> Expr
applyDiff d en@(L.ENew {}) =
  case d of
    L.NewField f -> over L.newFields (replaceField f) en
    L.DeleteField s -> over L.newFields (filter ((/= s) . (^. L.fieldName))) en
    L.OverrideMethod em -> over L.newBody (replaceMethod em) en
    L.DeleteMethod mname -> over L.newBody (deleteMethod mname) en
applyDiff d e = error "Can only apply diffs to new expressions"

applyDiffs :: [Diff] -> Expr -> Expr
applyDiffs ds e = foldl (flip applyDiff) e ds
