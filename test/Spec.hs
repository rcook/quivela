-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE NamedFieldPuns, QuasiQuotes, ScopedTypeVariables,
  TemplateHaskell #-}

import qualified Control.DeepSeq as DS
import Control.Exception (SomeException, catch)
import qualified Data.Map as M
import qualified Quivela.Language as L
import Quivela.Language (ProofPart(..))
import Quivela.Language
  ( Context(..)
  , Expr(..)
  , Proof(..)
  , ProofHint(..)
  , SymValue(..)
  , Type(..)
  , Value(..)
  , nop
  )
import qualified Quivela.Parse as P
import Quivela.Parse (parseExpr, parseProofPart)
import qualified Quivela.QuasiQuote as Q
import Quivela.QuasiQuote (prog, prog', prove')
import qualified Quivela.SymEval as S
import qualified Quivela.Util as U
import qualified Quivela.Verify as V
import Quivela.Verify ((≈), fieldEqual, fieldsEqual)
import qualified System.Environment as E
import qualified Test.HUnit as T
import Test.HUnit (Assertion, Counts(..), Test(TestCase, TestList), (~:))

-- Don't print garbage during tests.  If a test fails, debug it separately.
env = S.emptyVerifyEnv {S._debugFlag = False}

assertVerified :: String -> Expr -> Proof -> Test
assertVerified msg prefix proof =
  let t = do
        res <- prove' env prefix proof
        T.assertEqual msg 0 res
   in msg ~: TestCase t

assertError :: String -> IO a -> Test
assertError msg x =
  let t = do
        errored <-
          fmap DS.force $
          catch (x >> pure False) (\(_ :: SomeException) -> return True)
        if not errored
          then T.assertFailure $ "Should have failed: " ++ msg
          else T.assertBool "true" True
   in msg ~: TestCase t

assertEvalError :: String -> Expr -> Test
assertEvalError msg e =
  assertError msg . V.runVerify env $ S.symEval (e, L.emptyCtx, [])

assertEvalResult' :: String -> Context -> Expr -> Value -> Test
assertEvalResult' msg ctx e v =
  let a = do
        (res, _, _) <-
          S.singleResult <$> (V.runVerify env $ (S.symEval (e, ctx, [])))
        T.assertEqual msg res v
   in msg ~: TestCase a

assertEvalResult :: String -> Expr -> Value -> Test
assertEvalResult msg e v = assertEvalResult' msg L.emptyCtx e v

assertVerifyError :: String -> Expr -> Proof -> Test
assertVerifyError msg prefix proof = assertError msg $ prove' env prefix proof

assertParses :: String -> String -> Expr -> Test
assertParses msg progText e =
  msg ~: TestCase (T.assertEqual msg (P.parseExpr progText) e)

doesntVerify :: String -> Expr -> Proof -> Test
doesntVerify msg prefix proof =
  let a = do
        remaining <- prove' env prefix proof
        T.assertBool msg (remaining > 0)
   in msg ~: TestCase a

parserTests =
  map (U.uncurry3 assertParses) $
  [ ("integer constants", "23", EConst (VInt 23))
  , ("empty map literal", "map", EConst (VMap M.empty))
  , ( "unqualified function call"
    , "f(1)"
    , ECall
        {_callObj = EConst VNil, _callName = "f", _callArgs = [EConst (VInt 1)]})
  , ( "tuple with comparisons"
    , "<a, (b > c)>"
    , ETuple
        [ EVar "a"
        , ECall
            { _callObj = EConst VNil
            , _callName = ">"
            , _callArgs = [EVar "b", EVar "c"]
            }
        ])
  , ( "& is right-assoc"
    , "a & b & c"
    , ECall
        { _callObj = EConst VNil
        , _callName = "&"
        , _callArgs =
            [ EVar "a"
            , ECall
                { _callObj = EConst VNil
                , _callName = "&"
                , _callArgs = [EVar "b", EVar "c"]
                }
            ]
        })
  , ( "& and ,"
    , "a & b , c & d"
    , ECall
        { _callObj = EConst VNil
        , _callName = "&"
        , _callArgs =
            [ EVar "a"
            , ESeq
                (EVar "b")
                (ECall
                   { _callObj = EConst VNil
                   , _callName = "&"
                   , _callArgs = [EVar "c", EVar "d"]
                   })
            ]
        })
  , ( ", is right-assoc"
    , "a , b , c"
    , ESeq (EVar "a") (ESeq (EVar "b") (EVar "c")))
  , ( "& and , and | mix correctly"
    , "a | b , c & d"
    , ECall
        { _callObj = EConst VNil
        , _callName = "|"
        , _callArgs =
            [ EVar "a"
            , ESeq
                (EVar "b")
                (ECall
                   { _callObj = EConst VNil
                   , _callName = "&"
                   , _callArgs = [EVar "c", EVar "d"]
                   })
            ]
        })
  , ( "associativity of ! and |"
    , "!a | b"
    , ECall
        { _callObj = EConst VNil
        , _callName = "|"
        , _callArgs =
            [ ECall
                { _callObj = EConst VNil
                , _callName = "!"
                , _callArgs = [EVar "a"]
                }
            , EVar "b"
            ]
        })
  , ( "projections, indexing, and method calls in one expression"
    , "x[1].field.mtd(1, 2)"
    , ECall
        { _callObj = EProj (EIdx (EVar "x") (EConst (VInt 1))) "field"
        , _callName = "mtd"
        , _callArgs = [EConst (VInt 1), EConst (VInt 2)]
        })
  , ( "call on new in parentheses"
    , "(new () { method f(x: int) { x = <1, 2> } }).f(7)"
    , ECall
        { _callObj =
            ENew
              { _newFields = []
              , _newBody =
                  ESeq
                    (EMethod
                       { _emethodName = "f"
                       , _emethodArgs = [("x", TInt)]
                       , _emethodBody =
                           EAssign
                             { _lhs = EVar "x"
                             , _rhs = ETuple [EConst (VInt 1), EConst (VInt 2)]
                             }
                       , _emethodKind = L.NormalMethod
                       })
                    ENop
              }
        , _callName = "f"
        , _callArgs = [EConst (VInt 7)]
        })
  , ( "if expression with braces"
    , "if (1) { 3 } else { a + b }"
    , EIf
        (EConst (VInt 1))
        (EConst (VInt 3))
        (ECall
           { _callObj = EConst VNil
           , _callName = "+"
           , _callArgs = [EVar "a", EVar "b"]
           }))
  , ( "if without braces"
    , "if (x < y) a + b else 1+2"
    , EIf
        (ECall
           { _callObj = EConst VNil
           , _callName = "<"
           , _callArgs = [EVar "x", EVar "y"]
           })
        (ECall
           { _callObj = EConst VNil
           , _callName = "+"
           , _callArgs = [EVar "a", EVar "b"]
           })
        (ECall
           { _callObj = EConst VNil
           , _callName = "+"
           , _callArgs = [EConst (VInt 1), EConst (VInt 2)]
           }))
  ]

invalidCases =
  map
    (uncurry (`doesntVerify` nop))
    [ ( "trivial contradiction"
      , [prog| new() { method f() { 1 } } |] ≈
        [prog| new() { method f() { 2 } } |] :
        [])
    , ( "incorrect arithmetic"
      , [prog| new () { method f(x, y) { x + y } } |] ≈
        [prog| new () { method f(x, y) { x + x } } |] :
        [])
    , ( "variable capture in method inlining"
      , [prog| new () { method f(x) { y = 5 , y + x }
                  method g(x) { y = 6, f(x) + y } } |] ≈
        [prog| new () { method f(x) { y = 5 , y + x }
                  method g(x) { y = 6, (y = 5, y + x) + x } } |] :
        [])
    ]

-- Tests that should work but are currently broken.  We don't run these as
-- part of "stack test"
failingTests :: Test
failingTests =
  TestList
    [ assertVerified "map comprehension to modify existing map" nop $
      [prog|
new(i:int=0) {
  method f(y) { m = 0, m[y] = i, i++, m = [x ↦ m[x]+1 | m[x]], m[y] }
}|] ≈
      Hint [NoInfer, fieldEqual ["i"]] :
      [prog|
new(i:int=0) {
  method f(y) { if (!(0 == i)) { i++ } else { i++, 0 } }
} |] :
      []
    ]

tests :: Test
tests =
  TestList $
  parserTests ++
  invalidCases ++
  [ assertEvalError
      "assigning to constant variable"
      [prog'| new (const x = 0) { x = 1 } |]
  , assertEvalError "assigning to constant variable" $
    [prog'|
new (x=(new (const y=0) { 1 })) {
  x.y = 1
} |]
  , assertEvalError "assigning to constant field in typedecl'd object" $
    [prog'|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s = new S(), s.fs() } }
t = new T(s=new S()),
t.ft()
|]
  , assertEvalError "ill-typed assignment to object field" $
    [prog'|
new (x: int = 0) { x = <1, 2> } |]
  , assertEvalError "ill-typed assignment to object field" $
    [prog'|
new (x: <*, *> = 0) { x = 1 } |]
  , assertEvalError
      "ill-typed assignment to method parameter"
      [prog'|
(new () { method f(x: int) { x = <1, 2> } }).f(7)
|]
  , assertEvalError
      "ill-typed assignment using object type"
      [prog'|
type T = new () { method f() { 5 } }
(new(x: T) { method g() { x = 1 } }).g() |]
  , assertEvalError
      "ill-typed object creation"
      [prog'| new (x: <*, *> = 1) { 2 } |]
  , assertEvalError
      "ill-typed object creation using constructor"
      [prog'|
type T = new (x: int) { 2 }
new T(x=<1, 2>) |]
  , assertEvalResult
      "multiple indexing expressions in sequence"
      [prog'| a = 0 , a[0][1] = 5 , a[0][1] |]
      (VInt 5)
  , assertEvalResult
      "nested object field lookups"
      [prog'|
a = (new (const x=(new(const y = 5) {1})) {1} ),
a.x.y |]
      (VInt 5)
  , assertEvalResult
      "post-increment on object field"
      [prog'| x = (new(a=1) { 2 }) , <x.a++, x.a> |]
      (VTuple [VInt 1, VInt 2])
  , assertEvalResult
      "type declarations with parameters"
      [prog'| type T = new(x) { method f() { x } } , y = new T(x=5), y.f() |]
      (VInt 5)
  , assertEvalResult
      "Addresses can be used as symbolic values"
      [prog'| x = new() {}, y = new() {}, x + y |]
      (Sym (Add (Sym (Ref 1)) (Sym (Ref 2))))
  , assertEvalResult'
      "Decreasing allocation strategy should yield negative addresses"
      (L.emptyCtx {_ctxAllocStrategy = L.Decrease})
      (P.parseExpr "<new() {}, new() {}>")
      (VTuple [Sym {_symVal = Ref (-1)}, Sym {_symVal = Ref (-2)}])
  , assertEvalResult'
      "Decreasing allocation allows allocating objects in methods"
      L.emptyCtxRHS
      [prog'|
(new() {
method f(x) { obj = (new() { method g(m) { 1 } }), obj.g(x) & 1 }
}).f(5)|]
      (VInt 1)
  , assertVerifyError
      "verification should detect extraneous methods on one side"
      nop $
    [prog| new() { method f() { 1 } } |] ≈ [prog| new() { } |] : []
  , doesntVerify "if expression equivalence differing on one branch" nop $
    [prog| new() { method f(x) { if (x) { 7 } else { 8 } } } |] ≈
    [prog| new() { method f(x) { if (x) { 7 } else { 9 } } } |] :
    []
  , assertVerified "<= works" nop $
    [prog| new() { method f() { x <= x } } |] ≈
    [prog| new() { method f() { 1 } } |] :
    []
  , assertVerified "& well-behaved" nop $
    [prog| new() { method f(x, y) { 1 & x & y & 1 } } |] ≈
    [prog| new() { method f(x, y) { 1 & y & x & 1 } } |] ≈
    [prog| new() { method f(x, y) { y & x & 1 } } |] :
    []
  , assertVerified "simple equality invariant" nop $
    [prog| new (x=0) { method f() { <x, x> } } |] ≈
    Hint [fieldsEqual ["x"] ["y"]] :
    [prog| new (y=0) { method f() { <y, y> } } |] : []
  , assertVerified "simple const annotation" nop $
    [prog| new (const x=0) { method f() { x } } |] ≈
    [prog| new (const x=0) { method f() { 0 } } |] :
    []
  , assertVerified "addition is commutative and 0 is identity" nop $
    [prog| new () { method f(x, y) { 0 + x + 1 + y } } |] ≈
    [prog| new () { method f(x, y) { y + x + 1 } } |] :
    []
  , assertVerified "multiplication example" nop $
    [prog| new () { method f(x, y) { x * 3 * y } } |] ≈
    [prog| new () { method f(x, y) { (x + x + x) * y } } |] ≈
    [prog| new () { method f(x, y) { x * (y + y + y) } } |] :
    []
  , assertVerified "arithmetic example" nop $
    [prog| new () { method f(x:int, y, z) { x / 2 + y * z - x / 2 } } |] ≈
    [prog| new () { method f(x:int, y, z) { y * z } } |] :
    []
  , assertVerified "assignment to local variable" nop $
    [prog|
new() {
  method f(x) { c = x & c }
} |] ≈
    [prog|
new() {
  method f(x) { x }
} |] :
    []
  , assertVerified "tupling never returns 0" nop $
    [prog|
new() {
  method f(m) { <m> & 5 }
} |] ≈
    [prog|
new() {
  method f(m) { 5 }
}|] :
    []
  , assertVerified "if-else with symbolic condition" nop $
    [prog| new () { method f(x) { if (x) { 5 } else { 6 } } } |] ≈
    [prog| new () { method f(x) { if (!x) { 6 } else { 5 } } } |] :
    []
  , assertVerified "if-else with same value in both branches" nop $
    [prog| new () { method f() { if (x) 5 else 5 } } |] ≈
    [prog| new () { method f() { 5 } } |] :
    []
  , assertVerified "if-else with true guard" nop $
    [prog| new () { method f() { if (1) 7 else 8 } } |] ≈
    [prog| new () { method f() { 7 } } |] :
    []
  , assertVerified "if-else with false guard" nop $
    [prog| new() { method f() { if (2 < 1) 7 else 8 } } |] ≈
    [prog| new() { method f() { 8 } } |] :
    []
  , assertVerified "post-increment example 1" nop $
    [prog| new () { method f() { x = 0 , x++ , x } } |] ≈
    [prog| new () { method f() { 1 } } |] :
    []
  , assertVerified "post-increment example 2" nop $
    [prog| new () { method f(x) { x++ } } |] ≈
    [prog| new () { method f(x) { y = x , x = x + 1 , y } } |] :
    []
  , assertVerified "post-increment example 3" nop $
    [prog| new () { method f() { x = 0 , x++ } } |] ≈
    [prog| new () { method f() { 0 } } |] :
    []
  , assertVerified "post-increment in a map index" nop $
    [prog| new (m=0) { method f() { x = 0, m = 0, m[x++] = 42, m[0] } } |] ≈
    [prog| new () { method f() { 42 } } |] :
    []
  , assertVerified "less-than operator example" nop $
    [prog| new () { method f(x:int, y:int) { !(x < y) | !(x == y) } } |] ≈
    [prog| new () { method f(x:int, y:int) { 1 } } |] :
    []
  , assertVerified "Z(..) is idempotent" nop $
    [prog|
new() {
  method f(m) { Z(Z(m)) }
}|] ≈
    [prog|
new() {
  method f(m) { Z(m) }
}|] :
    []
  , assertVerified "call on symbolic object" nop $
    [prog|
type T = new() { method f() { 5 } }
new (x: T = new T()) {
  method g() { x.f() }
}|] ≈
    Hint [NoInfer] :
    [prog|
new () {
  method g() { 5 }
}|] :
    []
  , assertVerified "call on symbolic map value" nop $
    [prog|
type T = new() { method f() { 5 } }
new (x: map int T=map) {
  method g(i: int) {
    y = x[i] & y.f()
  }
} |] ≈
    Hint [fieldEqual ["x"]] :
    [prog|
type T = new() { method f() { 5 } }
new (x: map int T = map) {
  method g(i: int) {
    x[i] & 5
  }
} |] :
    []
  , assertVerified "object maps with an invariant" nop $
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
}|] ≈
    Hint [NoInfer, fieldEqual ["x"]] :
    [prog|
type T = new(p) { method f() { p } }
new (x: map * T = map) {
  method insert(i) {
    x[i] = new T(p=i)
  }
  method call(i) {
    x[i] & i
  }
}|] :
    []
  , assertVerified "object maps with invariant using field access" nop $
    [prog|
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
}|] ≈
    Hint [NoInfer, fieldEqual ["x"]] :
    [prog|
type T = new(p: *) { method f() { p } }
new (x: map * T = map) {
  method insert(i) {
    x[i] = new T(p=i)
  }
  method call(i) {
    x[i] & i
  }
}|] :
    []
  , assertVerified "commute two new(){} expressions used in result" nop $
    [prog|
new () { method f() { x = new() {}, y = new() {}, <x, y> } } |] ≈
    [prog|
new () { method f() { x = new() {}, y = new() {}, <y, x> } } |] :
    []
  , assertVerified
      "commute two new(){} expressions with an extra new on one side"
      nop $
    [prog|
new () { method f() { new() {} } } |] ≈
    Hint [IgnoreCache] :
    [prog|
new () { method f() { x = new() {}, y = new() {}, if (x) { y } else { y } } }|] :
    []
  , assertVerified "reason about new()s used only in path condition" nop $
    [prog|
new () { method f() { if (new(){}) { 5 } else { 6 } } }|] ≈
    Hint [IgnoreCache] :
    [prog|
new () { method f() { if (new(){}) { 5 } else { 6 } } }|] :
    []
  , assertVerified "syntactic sugar rnd() also commutes" nop $
    [prog| new() { method f() { x = rnd(), y = rnd(), <x, y> } } |] ≈
    Hint [IgnoreCache] :
    [prog| new() { method f() { x = rnd(), y = rnd(), <y, x> } } |] : []
  , assertVerified "basic set literals and membership" nop $
    [prog| new() { method f() { 1 ∈ {1} } } |] ≈
    [prog| new() { method f() { 1 } } |] :
    []
  , assertVerified "set membership in singleton set" nop $
    [prog| new() { method f(x) { x ∈ {1} } } |] ≈
    [prog| new() { method f(x) { x == 1 } } |] :
    []
  , assertVerified "trivial set comprehension" nop $
    [prog| new() { method f(y) { y ∈ {x | x ∈ {1}, 1} } } |] ≈
    [prog| new() { method f(y) { y == 1 } } |] :
    []
  , assertVerified "constant map comprehension" nop $
    [prog| new() { method f() { ([x ↦ 1 | 1])[5] } } |] ≈
    [prog| new() { method f() { 1 } } |] :
    []
  , assertVerified "map comprehension with another map in predicate" nop $
    [prog| new() { method f() { (m = map, m[1] = 42), ([x ↦ 42 | m[x]])[1] } } |] ≈
    [prog| new() { method f() { 42 } } |] :
    []
  , assertVerified
      "map comprehension using another map in predicate and mapping function"
      nop $
    [prog| new() { method f() { (m = map, m[1] = 42), ([x ↦ m[x]+1 | m[x]])[1] } } |] ≈
    [prog| new() { method f() { 43 } } |] :
    []
  , assertVerified "⊆ operation on concrete values" nop $
    [prog|
new() { method f() { m = 0, m[0] = 1, m[1] = 1, n = 0, n[0] = 1, n ⊆ m } } |] ≈
    [prog|
new() { method f() { 1 } } |] :
    []
  , assertVerified "⊆ operation on symbolic maps and indices" nop $
    [prog|
new(m: map * *) { method f(x) { n = m, n[x] = 1, m ⊆ n } } |] ≈
    [prog|
new() { method f(x) { 1 } } |] :
    []
  , assertVerified "local method" nop $
    [prog|
new() {
  local f() { 5 }
  method g() { f() }
} |] ≈
    [prog|
new() {
  method g() { 5 }
} |] :
    []
  , assertVerified "Pattern-matching behaves like tuple projection" nop $
    [prog|
new() {
  method f(x) { <a, b> = x, <b, a> }
} |] ≈
    [prog|
new() {
  method f(x) { <x`1, x`0> }
}|] :
    []
  , assertVerified "Pattern-matching remembers tuple size" nop $
    [prog|
new() {
  method f(x) { <a, b> = x, <a, b> }
}|] ≈
    [prog|
new() {
  method f(x) { x }
} |] :
    []
  , assertVerified "Nested symbolic objects" nop $
    [prog|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s.fs() } }
new() {
  method f() { t = new T(s=new S()), t.ft() }
}|] ≈
    [prog|
new() {
  method f() { 42 }
}|] :
    []
  , assertVerified "Nested symbolic objects in maps" nop $
    [prog|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s.fs() } }
new(m: map * T = 0) {
  method ins() { k = rnd(), m[k] = new T(s=new S()), 1 }
  method call(k) { m[k] & (x = m[k] & x.ft()) }
}|] ≈
    Hint [NoAddressBijection] :
    [prog|
type S = new() { method fs() { 42 } }
type T = new(const s: S) { method ft() { s.fs() } }
new(m: map * T = 0) {
  method ins() { k = rnd(), m[k] = new T(s=new S()), 1 }
  method call(k) { m[k] & (x = m[k] & 42) }
} |] :
    []
  , uncurry
      (assertVerified "calling uninterpreted function with same arguments") $
    ( [prog'| function f(arg) |]
    , [prog|
new() {
  method g() { f(5) }
}|] ≈
      [prog|
new() {
   method g() { f(1 + 4) }
}|] :
      [])
  , uncurry
      (doesntVerify "uninterpreted function called with different arguments") $
    ( [prog'| function f(arg) |]
    , [prog|
new() {
  method g() { f(1) }
}|] ≈
      [prog|
new() {
  method g() { f(2) }
}|] :
      [])
  , assertVerified "Type declaration with constant initializer" nop $
    [prog|
type EncT = new (const d=42) { 1 }
new () {
  method f() { (new EncT()).d }
}|] ≈
    [prog|
new() {
  method f() { 42 }
} |] :
    []
  , uncurry
      (assertVerified "Placing object and its parameter in different maps")
      ( [prog'|function uf(x)
type T = new(p) { 1 } |]
      , [prog|
new (m: map * T, d = 0) {
  method ins(u) {
    k = u & d[k] = k & f = new T(p=k) & m[k] = f & 1
  }
}|] ≈
        Hint [] :
        [prog|
  invariant i1(ek) { !ek | !m[ek] | (m[ek].p == d[ek]) }
  |] :
        [])
  , uncurry
      (assertVerified "Placing object and its parameter in different maps (2)")
      ( [prog'|
function uf(x) // : forall y. !!uf(y)
type T = new(p) { 1 } |]
      , [prog|
new (m: map * T, d = 0) {
  method ins() {
    k = rnd() & uk = uf(k) & d[uk] = k & f = new T(p=k) & m[uk] = f & 1
  }
  }|] ≈
        Hint [NoAddressBijection] :
        [prog|
           invariant i1(ek) { !ek | !m[ek] | (m[ek].p == d[ek]) }
           |] :
        [])
  , assertVerified "Dropping a call to rnd()" nop $
    [prog|new() { x = rnd(), rnd() }|] ≈ [prog|new() { rnd() }|] : []
  , assertVerified "uninitialized nested map" nop $
    [prog|
new() {
  method f(x, y) { a[x][y] = 5 & a[x][y] }
}|] ≈
    [prog|
new() {
  method f(x, y) { 5 }
}|] :
    []
  ]

main :: IO ()
main = do
  args <- E.getArgs
  let t =
        case args of
          [] -> tests
          ["bug"] -> failingTests
          _ -> error "Illegal arguments"
  counts@Counts {cases, tried, errors, failures} <- T.runTestTT t
  if failures > 0 || errors > 0
    then error $ "Failed tests: " ++ show counts
    else if tried /= cases
           then error $ "Not all tests ran: " ++ show counts
           else return ()
