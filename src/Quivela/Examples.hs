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
  [prog| new () { method f() { x = 0 , x++ } } |]
  ≈
  [prog| new () { method f() { 0 } } |]
  : []

postIncrExample2 :: [ProofPart]
postIncrExample2 =
  [prog| new () { method f(x) { x++ } } |]
  ≈
  [prog| new () { method f(x) { y = x , x = x + 1 , y } } |]
  : []

postIncrExample3 :: [ProofPart]
postIncrExample3 =
  [prog| new () { method f() { x = 0 , x++ , x } } |]
  ≈
  [prog| new () { method f() { 1 } } |]
  : []

postIncrementInMap :: [ProofPart]
postIncrementInMap =
  [prog| new (m=0) { method f() { x = 0, m = 0, m[x++] = 42, m[0] } } |]
  ≈
  [prog| new (m=0) { method f() { 42 } } |]
  : []

leExample :: [ProofPart]
leExample =
  [prog| new () { method f(x:int, y:int) { !(x < y) | !(x == y) } } |]
  ≈
  [prog| new () { method f(x:int, y:int) { 1 } } |]
  : []


doubleIdx :: Expr
doubleIdx = [prog'| a = 0 , a[0][1] = 5 , a[0][1] |]

doubleFieldDeref :: Expr
doubleFieldDeref = [prog'|
a = (new (const x=(new(const y = 5) {1})) {1} ),
a.x.y |]

incrementFieldDeref :: Expr
incrementFieldDeref = [prog'| x = (new(a=1) { 2 }) , x.a++ |]

typedeclTest :: Expr
typedeclTest = [prog'| type T = new(x) { method f() { x } } , y = new T(x=5), y.f() |]

symcallTest :: [ProofPart]
symcallTest =
  [prog|
type T = new() { method f() { 5 } }
new (x: T = new T()) {
  method g() { x.f() }
}|]
  ≈ Hint [NoInfer]:
  [prog|
new () {
  method g() { 5 }
}|]
  : []

symcallMap :: [ProofPart]
symcallMap =
  [prog|
type T = new() { method f() { 5 } }
new (x: map int T=map) {
  method g(i: int) {
    y = x[i] & y.f()
  }
} |]
  ≈ Hint [fieldEqual ["x"]]:
  [prog|
type T = new() { method f() { 5 } }
new (x: map int T = map) {
  method g(i: int) {
    x[i] & 5
  }
} |]
  : []

symcallMapParam :: [ProofPart]
symcallMapParam =
  [prog|
type T = new(p: int) { method f() { p } }
new (x: map int T = map) {
  method insert(i:int) {
    x[i] = new T(p=i)
  }
  method call(i: int) {
    y = x[i] & y.f()
  }
  invariant par(i: int) {
    !x[i] | (x[i].f() == i)
  }
}|]
  ≈ Hint [NoInfer, fieldEqual ["x"]]:
  [prog|
type T = new(p: int) { method f() { p } }
new (x: map int T = map) {
  method insert(i: int) {
    x[i] = new T(p=i)
  }
  method call(i: int) {
    x[i] & i
  }
}|]
  : []

extraMethodsTest :: [ProofPart]
extraMethodsTest =
  [prog| new() { method f() { 1 } } |]
  ≈
  [prog| new() { } |]
  : []

illTypedConstrAssign :: Expr
illTypedConstrAssign =
  [prog'|
type T = new () { method f() { 5 } }
(new(x: T) { method g() { x = 1 } }).g() |]

illTypedObjectCreation :: Expr
illTypedObjectCreation =
  [prog'| new (x: <*, *> = 1) { 2 } |]

illTypedObjectCreationNamed :: Expr
illTypedObjectCreationNamed =
  [prog'|
type T = new (x: int) { 2 }
new T(x=<1, 2>) |]
