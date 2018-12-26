-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
module Quivela.Diff
  ( applyDiffs
  ) where

import qualified Control.Lens as Lens
import Control.Lens ((^.))
import qualified Data.List as L
import qualified Quivela.Language as Q
import Quivela.Language (Diff, Expr, Field, Var)
import Quivela.Prelude

seqToList :: Expr -> [Expr]
seqToList Q.ENop = []
seqToList (Q.ESeq e1 e2) = e1 : seqToList e2
seqToList _ = error "Invalid argument to seqToList"

replaceMethod :: Expr -> Expr -> Expr
replaceMethod emtd ebody
  | L.any
     (\e ->
        case e of
          mtd'@(Q.EMethod {}) -> mtd' ^. Q.emethodName == emtd ^. Q.emethodName
          _ -> False)
     bodyExprs = L.foldr Q.ESeq Q.ENop $ fmap replace bodyExprs
  where
    replace mtd'@(Q.EMethod {})
      | mtd' ^. Q.emethodName == emtd ^. Q.emethodName = emtd
      | otherwise = mtd'
    replace e = e
    bodyExprs = seqToList ebody
replaceMethod emtd ebody = L.foldr Q.ESeq Q.ENop (seqToList ebody ++ [emtd])

replaceField :: Field -> [Field] -> [Field]
replaceField newField oldFields
  | L.any
     (\oldField -> oldField ^. Q.fieldName == newField ^. Q.fieldName)
     oldFields = fmap replace oldFields
  where
    replace oldField
      | oldField ^. Q.fieldName == newField ^. Q.fieldName = newField
      | otherwise = oldField
replaceField newField oldFields = oldFields ++ [newField]

deleteMethod :: Var -> Expr -> Expr
deleteMethod mtdName body =
  Lens.over
    (Lens.iso seqToList (L.foldr Q.ESeq Q.ENop))
    (L.filter
       (\e ->
          case e of
            oldMtd@Q.EMethod {} -> oldMtd ^. Q.emethodName /= mtdName
            _ -> True))
    body

applyDiff :: Diff -> Expr -> Expr
applyDiff d en@(Q.ENew {}) =
  case d of
    Q.NewField f -> Lens.over Q.newFields (replaceField f) en
    Q.DeleteField s -> Lens.over Q.newFields (L.filter ((/= s) . (^. Q.fieldName))) en
    Q.OverrideMethod em -> Lens.over Q.newBody (replaceMethod em) en
    Q.DeleteMethod mname -> Lens.over Q.newBody (deleteMethod mname) en
applyDiff _ _ = error "Can only apply diffs to new expressions"

applyDiffs :: [Diff] -> Expr -> Expr
applyDiffs ds e = L.foldl (flip applyDiff) e ds
