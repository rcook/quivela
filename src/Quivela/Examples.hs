{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Quivela.Examples where

import Control.Lens
import Control.Lens.At
import qualified Data.Map as M

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

objectMap :: [ProofPart]
objectMap =
  [prog|
new(x: map int ObjT=0) {
  method add(idx: int) {
    x[idx] = (new () { method foo() { 42 } })
  };
  method call(idx: int) {
    (x[idx]).foo()
  }
}|]
    ≈ Hint [ fieldEqual ["x"] ]:
    [prog|
new(x: map int ObjT=0) {
  method add(idx: int) {
    x[idx] = (new () { method foo() { 42 } })
  };
  method call(idx: int) {
    x[idx]  & 42
  }
}
|] :[]

objectMapEnv :: VerifyEnv
objectMapEnv = typeDenotations . at "ObjT" ?~ ObjectType methodMap $ emptyVerifyEnv
  where methodMap = M.fromList [("foo", \_ ctx -> [(VInt 42, ctx, [])])]


addExample :: [ProofPart]
addExample =
  [prog| new () { method f(x, y) { 0 + x + 1 + y } } |]
  ≈
  [prog| new () { method f(x, y) { y + x + 1 } } |]
  : []

mulExample :: [ProofPart]
mulExample =
  [prog| new () { method f(x, y) { x * 3 * y } } |]
  ≈
  [prog| new () { method f(x, y) { (x + x + x) * y } } |]
  ≈
  [prog| new () { method f(x, y) { x * (y + y + y) } } |]
  : []

arithExample :: [ProofPart]
arithExample =
  [prog| new () { method f(x:int, y, z) { x / 2 + y * z - x / 2 } } |]
  ≈
  [prog| new () { method f(x:int, y, z) { y * z } } |]
  : []

postIncrExample1 :: [ProofPart]
postIncrExample1 =
  [prog| new () { method f() { x = 0 ; x++ } } |]
  ≈
  [prog| new () { method f() { 0 } } |]
  : []

postIncrExample2 :: [ProofPart]
postIncrExample2 =
  [prog| new () { method f(x) { x++ } } |]
  ≈
  [prog| new () { method f(x) { y = x ; x = x + 1 ; y } } |]
  : []

postIncrExample3 :: [ProofPart]
postIncrExample3 =
  [prog| new () { method f() { x = 0 ; x++ ; x } } |]
  ≈
  [prog| new () { method f() { 1 } } |]
  : []
