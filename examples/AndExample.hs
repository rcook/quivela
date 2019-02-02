{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Prelude
import Quivela
import Quivela.Language
import System.Exit

andExample :: [ProofPart]
andExample =
  [prog| new() { method f(x, y) { 1 & x & y & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { 1 & y & x & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { y & x & 1 } } |]
  : []

main :: IO ()
main = do
  result <- prove' emptyVerifyEnv nop andExample
  if result /= 0
    then exitFailure
    else exitSuccess
