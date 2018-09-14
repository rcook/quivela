{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Quivela.Examples where

import Control.Lens
import Control.Lens.At
import qualified Data.Map as M

import Quivela

andExample :: Proof
andExample =
  [prog| new() { method f(x, y) { 1 & x & y & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { 1 & y & x & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { y & x & 1 } } |]
  : []

eqInvExample :: Proof
eqInvExample =
  [prog| new (x=0) { method f() { <x, x> } } |]
  ≈ Hint [ fieldsEqual ["x"] ["y"] ]:
  [prog| new (y=0) { method f() { <y, y> } } |]
  : []

constExample :: Proof
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

addExample :: Proof
addExample =
  [prog| new () { method f(x, y) { 0 + x + 1 + y } } |]
  ≈
  [prog| new () { method f(x, y) { y + x + 1 } } |]
  : []

mulExample :: Proof
mulExample =
  [prog| new () { method f(x, y) { x * 3 * y } } |]
  ≈
  [prog| new () { method f(x, y) { (x + x + x) * y } } |]
  ≈
  [prog| new () { method f(x, y) { x * (y + y + y) } } |]
  : []

arithExample :: Proof
arithExample =
  [prog| new () { method f(x:int, y, z) { x / 2 + y * z - x / 2 } } |]
  ≈
  [prog| new () { method f(x:int, y, z) { y * z } } |]
  : []

postIncrExample1 :: Proof
postIncrExample1 =
  [prog| new () { method f() { x = 0 , x++ } } |]
  ≈
  [prog| new () { method f() { 0 } } |]
  : []

postIncrExample2 :: Proof
postIncrExample2 =
  [prog| new () { method f(x) { x++ } } |]
  ≈
  [prog| new () { method f(x) { y = x , x = x + 1 , y } } |]
  : []

postIncrExample3 :: Proof
postIncrExample3 =
  [prog| new () { method f() { x = 0 , x++ , x } } |]
  ≈
  [prog| new () { method f() { 1 } } |]
  : []

postIncrementInMap :: Proof
postIncrementInMap =
  [prog| new (m=0) { method f() { x = 0, m = 0, m[x++] = 42, m[0] } } |]
  ≈
  [prog| new (m=0) { method f() { 42 } } |]
  : []

leExample :: Proof
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
incrementFieldDeref = [prog'| x = (new(a=1) { 2 }) , <x.a++, x.a> |]

typedeclTest :: Expr
typedeclTest = [prog'| type T = new(x) { method f() { x } } , y = new T(x=5), y.f() |]

symcallTest :: Proof
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

symcallMap :: Proof
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

symcallMapParam :: Proof
symcallMapParam =
  [prog|
type T = new(p) { method f() { p } }
new (x: map * T = map) {
  method insert(i) {
    x[i] = new T(p=i)
  }
  method call(i) {
    y = x[i] & y.f()
  }
  invariant par(i) {
    !x[i] | (x[i].f() == i)
  }
}|]
  ≈ Hint [NoInfer, fieldEqual ["x"]]:
  [prog|
type T = new(p) { method f() { p } }
new (x: map * T = map) {
  method insert(i) {
    x[i] = new T(p=i)
  }
  method call(i) {
    x[i] & i
  }
}|]
  : []

mapInvariantField :: Proof
mapInvariantField = [prog|
type T = new(p: *) { method f() { p } }
new (x: map * T = map) {
  method insert(i) {
    x[i] = new T(p=i)
  }
  method call(i) {
    y = x[i] & y.f()
  }
  invariant par(i) {
    !x[i] | (x[i].p == i)
  }
}|]
  ≈ Hint [NoInfer, fieldEqual ["x"]]:
  [prog|
type T = new(p: *) { method f() { p } }
new (x: map * T = map) {
  method insert(i) {
    x[i] = new T(p=i)
  }
  method call(i) {
    x[i] & i
  }
}|]
  : []

extraMethodsTest :: Proof
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

incorrectVerify1 :: Proof
incorrectVerify1 =
  [prog| new() { method f() { 1 } } |]
  ≈
  [prog| new() { method f() { 2 } } |]
  : []

incorrectVerify2 :: Proof
incorrectVerify2 =
  [prog| new () { method f(x, y) { x + y } } |]
  ≈
  [prog| new () { method f(x, y) { x + x } } |]
  : []

incorrectMethodInlineCapture :: Proof
incorrectMethodInlineCapture =
  [prog| new () { method f(x) { y = 5 , y + x }
                  method g(x) { y = 6, f(x) + y } } |]
  ≈
  [prog| new () { method f(x) { y = 5 , y + x }
                  method g(x) { y = 6, (y = 5, y + x) + x } } |]
  : []

ifSymbolic :: Proof
ifSymbolic =
  [prog| new () { method f(x) { if (x) { 5 } else { 6 } } } |]
  ≈
  [prog| new () { method f(x) { if (!x) { 6 } else { 5 } } } |]
  : []

ifSimp :: Proof
ifSimp =
  [prog| new () { method f() { if (x) 5 else 5 } } |]
  ≈
  [prog| new () { method f() { 5 } } |]
  : []

ifConcreteTrue :: Proof
ifConcreteTrue =
  [prog| new () { method f() { if (1) 7 else 8 } } |]
  ≈
  [prog| new () { method f() { 7 } } |]
  : []

ifConcreteFalse :: Proof
ifConcreteFalse =
  [prog| new() { method f() { if (2 < 1) 7 else 8 } } |]
  ≈
  [prog| new() { method f() { 8 } } |]
  : []

ifEqvFalse :: Proof
ifEqvFalse =
  [prog| new() { method f(x) { if (x) { 7 } else { 8 } } } |]
  ≈
  [prog| new() { method f(x) { if (x) { 7 } else { 9 } } } |]
  : []

commuteNews :: Proof
commuteNews =
  [prog|
new () { method f() { x = new() {}, y = new() {}, <x, y> } } |]
  ≈
  [prog|
new () { method f() { x = new() {}, y = new() {}, <y, x> } } |]
  : []

addressesSymbolic :: Expr
addressesSymbolic = [prog'| x = new() {}, y = new() {}, x + y |]

commuteNewPathCondition :: Proof
commuteNewPathCondition =
  [prog|
new () { method f() { new() {} } } |]
  ≈ Hint [IgnoreCache]:
  [prog|
new () { method f() { x = new() {}, y = new() {}, if (x) { y } else { y } } }|]
  : []

commuteNewContradictoryPath :: Proof
commuteNewContradictoryPath =
  [prog|
new () { method f() { if (new(){}) { 5 } else { 6 } } }|]
  ≈ Hint [IgnoreCache]:
  [prog|
new () { method f() { if (new(){}) { 5 } else { 6 } } }|]
  : []

commuteRands :: Proof
commuteRands =
  [prog| new() { method f() { x = rnd(), y = rnd(), <x, y> } } |]
  ≈ Hint [IgnoreCache]:
  [prog| new() { method f() { x = rnd(), y = rnd(), <y, x> } } |]
  : []

leTaut :: Proof
leTaut =
  [prog| new() { method f() { x <= x } } |]
  ≈
  [prog| new() { method f() { 1 } } |]
  : []

setInTest :: Proof
setInTest =
  [prog| new() { method f() { 1 ∈ {1} } } |]
  ≈
  [prog| new() { method f() { 1 } } |]
  : []

setInTest2 :: Proof
setInTest2 =
  [prog| new() { method f(x) { x ∈ {1} } } |]
  ≈
  [prog| new() { method f(x) { x == 1 } } |]
  : []

setComprTest1 :: Proof
setComprTest1 =
  [prog| new() { method f(y) { y ∈ {x | x ∈ {1}, 1} } } |]
  ≈
  [prog| new() { method f(y) { y == 1 } } |]
  : []

mapComprTest1 :: Proof
mapComprTest1 =
  [prog| new() { method f() { ([x ↦ 1 | 1])[5] } } |]
  ≈
  [prog| new() { method f() { 1 } } |]
  : []

mapComprTest2 :: Proof
mapComprTest2 =
  [prog| new() { method f() { (m = map, m[1] = 42), ([x ↦ 42 | m[x]])[1] } } |]
  ≈
  [prog| new() { method f() { 42 } } |]
  : []

mapComprTest3 :: Proof
mapComprTest3 =
  [prog| new() { method f() { (m = map, m[1] = 42), ([x ↦ m[x]+1 | m[x]])[1] } } |]
  ≈
  [prog| new() { method f() { 43 } } |]
  : []

mapComprTest4 :: Proof
mapComprTest4 =
  [prog|
new(i:int=0) {
  method f(y) { m = 0, m[y] = i, m = [x ↦ m[x]+1 | m[x]], m[y] }
}|]
  ≈ Hint [NoInfer, fieldEqual ["i"]]:
  [prog|
new(i:int=0) {
  method f(y) { !(0 == i) & i++, i }
} |]
  : []

constSubmap :: Proof
constSubmap =
  [prog|
new() { method f() { m = 0, m[0] = 1, m[1] = 1, n = 0, n[0] = 1, n ⊆ m } } |]
  ≈
  [prog|
new() { method f() { 1 } } |]
  : []

paramSubmap :: Proof
paramSubmap =
  [prog|
new(m: map * *) { method f(x) { n = m, n[x] = 1, m ⊆ n } } |]
  ≈
  [prog|
new() { method f(x) { 1 } } |]
  : []

localMethodExample :: Proof
localMethodExample =
  [prog|
new() {
  local f() { 5 }
  method g() { f() }
} |]
  ≈
  [prog|
new() {
  method g() { 5 }
} |]
  : []

patMatch1 :: Proof
patMatch1 =
  [prog|
new() {
  method f(x) { <a, b> = x, <b, a> }
} |]
  ≈
  [prog|
new() {
  method f(x) { <x`1, x`0> }
}|]
  : []

patMatch2 :: Proof
patMatch2 =
  [prog|
new() {
  method f(x) { <a, b> = x, <a, b> }
}|]
  ≈
  [prog|
new() {
  method f(x) { x }
} |]
  :[]

zIdempotent :: Proof
zIdempotent =
  [prog|
new() {
  method f(m) { Z(Z(m)) }
}|]
  ≈
  [prog|
new() {
  method f(m) { Z(m) }
}|]
  : []

uninitializedNestedMap :: Proof
uninitializedNestedMap =
  [prog|
new() {
  method f(x, y) { a[x][y] = 5 & a[x][y] }
}|]
  ≈
  [prog|
new() {
  method f(x, y) { 5 }
}|]
  :[]

tuplingAnd :: Proof
tuplingAnd =
  [prog|
new() {
  method f(m) { <m> & 5 }
} |]
  ≈
  [prog|
new() {
  method f(m) { 5 }
}|]
  :[]

assignAnd :: Proof
assignAnd =
  [prog|
new() {
  method f(x) { c = x & c }
} |]
  ≈
  [prog|
new() {
  method f(x) { x }
} |]
  : []

decreaseAlloc :: Expr
decreaseAlloc = [prog'|
(new() {
method f(x) { obj = (new() { method g(m) { 1 } }), obj.g(x) & 1 }
}).f(5)|]

assignConstTypeDecl :: Expr
assignConstTypeDecl = [prog'|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s = new S(), s.fs() } }
t = new T(s=new S()),
t.ft()
|]


nestedObjs :: Proof
nestedObjs = [prog|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s.fs() } }
new() {
  method f() { t = new T(s=new S()), t.ft() }
}|]
  ≈ [prog|
new() {
  method f() { 42 }
}|]
  : []

nestedObjMap :: Proof
nestedObjMap = [prog|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s.fs() } }
new(m: map * T = 0) {
  method ins() { k = rnd(), m[k] = new T(s=new S()), 1 }
  method call(k) { m[k] & (x = m[k] & x.ft()) }
}|]
  ≈
  [prog|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s.fs() } }
new(m: map * T = 0) {
  method ins() { k = rnd(), m[k] = new T(s=new S()), 1 }
  method call(k) { m[k] & 42 }
} |]
  : []


fundeclTest1 :: (Expr, Proof)
fundeclTest1 = ([prog'| function f(arg) |], [prog|
new() {
  method g() { f(5) }
}|]
  ≈
  [prog|
new() {
   method g() { f(1 + 4) }
}|]
  : [])

fundeclTest2 :: (Expr, Proof)
fundeclTest2 = ([prog'| function f(arg) |], [prog|
new() {
  method g() { f(1) }
}|]
  ≈
  [prog|
new() {
  method g() { f(2) }
}|] : [])
