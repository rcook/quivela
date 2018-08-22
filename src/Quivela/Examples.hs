{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Quivela.Examples where

import Quivela

andExample :: [ProofPart]
andExample =
  [prog| new() { method f(x, y) { 1 & x & y & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { 1 & y & x & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { y & x & 1 } } |]
  : []

eqInvExample :: [ProofPart]
eqInvExample =
  [prog| new (x=0) { method f() { <x, x> } } |]
  ≈ Hint [ fieldsEqual ["x"] ["y"] ]:
  [prog| new (y=0) { method f() { <y, y> } } |]
  : []

constExample :: [ProofPart]
constExample =
  [prog| new (const x=0) { method f() { x } } |]
  ≈
  [prog| new (const x=0) { method f() { 0 } } |]
  :[]

assignConst :: Expr
assignConst = [prog'| new (const x = 0) { x = 1 } |]

assignConst' :: Expr
assignConst' = [prog'|
new (x=(new (const y=0) { 1 })) {
  x.y = 1
} |]

illTypedAssign :: Expr
illTypedAssign = [prog'|
new (x: int = 0) { x = <1, 2> } |]

illTypedAssign' :: Expr
illTypedAssign' = [prog'|
new (x: <*, *> = 0) { x = 1 } |]

illTypedParamAssign :: Expr
illTypedParamAssign = [prog'|
(new () { method f(x: int) { x = <1, 2> } }).f(7)
|]
