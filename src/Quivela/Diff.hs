module Quivela.Diff where

import Control.Lens

import Quivela.Language

seqToList ENop = []
seqToList (ESeq e1 e2) = e1 : seqToList e2
seqToList _ = error "Invalid argument to seqToList"

replaceMethod :: Expr -> Expr -> Expr
replaceMethod emtd ebody
  | any (\e -> case e of
            mtd'@(EMethod{}) -> mtd' ^. emethodName == emtd ^. emethodName
            _ -> False) bodyExprs = foldr ESeq ENop $ map replace bodyExprs
  where replace mtd'@(EMethod{})
          | mtd' ^. emethodName == emtd ^. emethodName = emtd
          | otherwise = mtd'
        replace e = e
        bodyExprs = seqToList ebody
replaceMethod emtd ebody = foldr ESeq ENop (seqToList ebody ++ [emtd])

replaceField :: Field -> [Field] -> [Field]
replaceField newField oldFields
  | any (\oldField -> oldField ^. fieldName == newField ^. fieldName) oldFields =
      map replace oldFields
  where replace oldField | oldField ^. fieldName == newField ^. fieldName = newField
                         | otherwise = oldField
replaceField newField oldFields = oldFields ++ [newField]

applyDiff :: Diff -> Expr -> Expr
applyDiff d en@(ENew{}) =
  case d of
    NewField f -> over newFields (replaceField f) en
    DeleteField s -> over newFields (filter (not . (==s) . (^. fieldName))) en
    OverrideMethod em -> over newBody (replaceMethod em) en
applyDiff d e = error "Can only apply diffs to new expressions"

applyDiffs :: [Diff] -> Expr -> Expr
applyDiffs ds e = foldl (flip applyDiff) e ds
