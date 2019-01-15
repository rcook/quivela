-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
module Quivela.Util
  ( PartialEq((===), elemPartial)
  , foreachM
  , heredoc
  , intercept
  , uncurry3
  ) where

import qualified Control.Monad.Writer.Class as MonadWriter
import Control.Monad.Writer.Class (MonadWriter)
import qualified Data.List as L
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH (Exp, Q)
import qualified Language.Haskell.TH.Quote as TH
import Quivela.Prelude

-- | A type class for types that only support equality partially. Whenever @(a === b) == Just x@,
-- then the boolean x indicates that a and b are equal/unequal. Otherwise, it cannot be determined
-- if the two values are equal
class PartialEq a where
  (===) :: a -> a -> Maybe Bool
  elemPartial :: a -> [a] -> Bool
  elemPartial x ys = L.any ((== Just True) . (=== x)) ys

heredocExpr :: String -> Q Exp
heredocExpr s = TH.litE . TH.StringL $ s

-- | A quasi-quoter allowing for multi-line string literals
heredoc :: TH.QuasiQuoter
heredoc = TH.QuasiQuoter heredocExpr invalidUse invalidUse invalidUse
  where
    invalidUse _ = error "Invalid context for heredoc quasi-quotation"

foreachM :: (Monad m) => m [a] -> (a -> m [b]) -> m [b]
foreachM s act = do
  xs <- s
  ys <- mapM act xs
  return $ L.concat ys

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

-- | Runs an action in a writer monad, but suppresses its output and instead
-- returns it in the results
intercept :: MonadWriter w m => m a -> m (a, w)
intercept action = MonadWriter.censor (const mempty) (MonadWriter.listen action)
