-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE CPP, QuasiQuotes #-}

import Quivela
import qualified System.Exit as E

#define FOO(x, y) <x, y>

program =
  prove'
    emptyVerifyEnv
    nop $
    [prog| new (x=0) { method f() { FOO(a, _) = FOO(x, x) & a } } |] ≈
    Hint [fieldsEqual ["x"] ["y"]] :
    [prog| new (y=0) { method f() { FOO(b, _) = FOO(y, y) & b } } |] : []

main :: IO ()
main = do
  n <- program
  if n == 0 then E.exitSuccess else E.exitFailure
