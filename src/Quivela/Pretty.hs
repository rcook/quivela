module Quivela.Pretty
  ( angled
  , binop
  , const
  , map
  , mapP
  , object
  , record
  , set
  , setP
  , show
  , step
  ) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as P
import Data.Text.Prettyprint.Doc (Doc, Pretty(pretty), (<+>), (<>))
import Data.Text.Prettyprint.Doc.Render.String as Doc
import Quivela.Prelude hiding (const, map, show)

step :: Int
step = 2

width :: Int
width = 120

ribbon :: Double
ribbon = 1.0

record :: [(String, Doc ann)] -> Doc ann
record xs =
  object $ L.map (\(l, r) -> P.nest step (pretty l <> P.colon <> P.line <> r)) xs

map :: [(Doc ann, Doc ann)] -> Doc ann
map xs =
  if L.null xs
    then pretty "empty"
    else P.vcat (L.map (\(l, r) -> l <+> pretty "↦" <+> r) xs)

mapP :: (Pretty a, Pretty b) => Map a b -> Doc ann
mapP m = map $ L.map (\(l, r) -> (pretty l, pretty r)) (M.toList m)

set :: [Doc ann] -> Doc ann
set xs = P.lbrace <+> P.align (P.vcat xs) <+> P.rbrace

setP :: Pretty a => Set a -> Doc ann
setP s = set (L.map pretty $ Set.toList s)

binop :: (Pretty a, Pretty b) => String -> a -> b -> Doc ann
binop s l r = pretty l <+> pretty s <+> pretty r

object :: [Doc ann] -> Doc ann
object xs = P.align $ (P.hang step (P.lbrace <> P.line <> P.vcat xs)) <> P.line <> P.rbrace

const :: Bool -> Doc ann
const True = pretty "const" <> P.space
const False = mempty

show :: Doc ann -> String
show d =
  Doc.renderString $
  P.layoutPretty (P.LayoutOptions (P.AvailablePerLine width ribbon)) d

angled :: [Doc ann] -> Doc ann
angled = P.encloseSep P.langle P.rangle P.comma
