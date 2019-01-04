-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE LambdaCase #-}

module Quivela.Diff
  ( applyDiffs
  ) where

import qualified Control.Lens as Lens
import Control.Lens ((^.))
import qualified Data.List as L
import qualified Quivela.Language as Q
import Quivela.Language (Diff, Expr, Field, Var)
import Quivela.Prelude

replaceMethod :: Expr -> Expr -> Expr
replaceMethod emtd ebody = Q.exprsToSeq (L.reverse exprs'')
  where
    f (True, exprs) expr = (True, expr : exprs)
    f (False, exprs) expr@(Q.EMethod {})
      | expr ^. Q.emethodName == emtd ^. Q.emethodName = (True, emtd : exprs)
      | otherwise = (False, expr : exprs)
    f (False, exprs) expr = (False, expr : exprs)
    (changed, exprs') = L.foldl f (False, []) (Q.seqToExprs ebody)
    exprs'' =
      if changed
        then exprs'
        else emtd : exprs'

replaceField :: Field -> [Field] -> [Field]
replaceField newField oldFields = L.reverse fields''
  where
    f (True, fields) field = (True, field : fields)
    f (False, fields) field
      | field ^. Q.fieldName == newFieldName = (True, newField : fields)
      | otherwise = (False, field : fields)
    (changed, fields') = L.foldl f (False, []) oldFields
    fields'' =
      if changed
        then fields'
        else newField : fields'
    newFieldName = newField ^. Q.fieldName

deleteMethod :: Var -> Expr -> Expr
deleteMethod mtdName = Q.exprsToSeq . f . Q.seqToExprs
  where
    f =
      L.filter
        (\case
           oldMtd@Q.EMethod {} -> oldMtd ^. Q.emethodName /= mtdName
           _ -> True)

applyDiff :: Diff -> Expr -> Expr
applyDiff d en@(Q.ENew {}) =
  case d of
    Q.NewField f -> Lens.over Q.newFields (replaceField f) en
    Q.DeleteField s ->
      Lens.over Q.newFields (L.filter ((/= s) . (^. Q.fieldName))) en
    Q.OverrideMethod em -> Lens.over Q.newBody (replaceMethod em) en
    Q.DeleteMethod mname -> Lens.over Q.newBody (deleteMethod mname) en
applyDiff _ _ = error "Can only apply diffs to new expressions"

applyDiffs :: [Diff] -> Expr -> Expr
applyDiffs ds e = L.foldl (flip applyDiff) e ds
