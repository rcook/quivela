-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE NamedFieldPuns, QuasiQuotes, ScopedTypeVariables,
  TemplateHaskell #-}

import qualified Control.DeepSeq as DeepSeq
import qualified Control.Exception as Exception
import Control.Exception (SomeException)
import qualified Control.Lens as Lens
import Control.Lens ((&), (.~))
import qualified Data.Map as M
import Prelude
import Quivela
import Quivela.Language
  ( Context(..)
  , Expr(..)
  , Method(..)
  , Proof
  , ProofHint(..)
  , ProofPart(..)
  , SymValue(..)
  , Type(..)
  , Value(..)
  )
import qualified Quivela.Language as Q
import qualified Quivela.Parse as Q
import qualified Quivela.SymEval as Q
import qualified Quivela.Util as Q
import qualified Quivela.Verify as Q
import qualified System.Environment as Environment
import qualified Test.HUnit as T
import Test.HUnit (Assertion, Counts(..), Test(TestCase, TestList), (~:))

-- Don't print garbage during tests.  If a test fails, debug it separately.
env = Q.emptyVerifyEnv & Q.debugFlag .~ False

assertVerified :: String -> Expr -> Proof -> Test
assertVerified msg prefix proof =
  let t = do
        res <- prove' env prefix proof
        T.assertEqual msg 0 res
   in msg ~: TestCase t

assertVerifiedDebug :: String -> Expr -> Proof -> Test
assertVerifiedDebug msg prefix proof =
  let t = do
        res <-
          prove' (Q.emptyVerifyEnv & Q.writeAllVCsToFile .~ True) prefix proof
        T.assertEqual msg 0 res
   in msg ~: TestCase t

assertError :: String -> IO a -> Test
assertError msg x =
  let t = do
        errored <-
          fmap DeepSeq.force $
          Exception.catch
            (x >> pure False)
            (\(_ :: SomeException) -> return True)
        if not errored
          then T.assertFailure $ "Should have failed: " ++ msg
          else T.assertBool "true" True
   in msg ~: TestCase t

assertEvalError :: String -> Expr -> Test
assertEvalError msg e =
  assertError msg . Q.runVerify env $ Q.symEval (e, Q.emptyCtx, [])

assertEvalResult' :: String -> Context -> Expr -> Value -> Test
assertEvalResult' msg ctx e v =
  let a = do
        (res, _, _) <-
          Q.singleResult <$> (Q.runVerify env $ (Q.symEval (e, ctx, [])))
        T.assertEqual msg res v
   in msg ~: TestCase a

assertEvalResult :: String -> Expr -> Value -> Test
assertEvalResult msg e v = assertEvalResult' msg Q.emptyCtx e v

assertVerifyError :: String -> Expr -> Proof -> Test
assertVerifyError msg prefix proof = assertError msg $ prove' env prefix proof

assertParses :: String -> String -> Expr -> Test
assertParses msg progText e =
  msg ~: TestCase (T.assertEqual msg (Q.parseExpr progText) e)

doesntVerify :: String -> Expr -> Proof -> Test
doesntVerify msg prefix proof =
  let a = do
        remaining <- prove' env prefix proof
        T.assertBool msg (remaining > 0)
   in msg ~: TestCase a

parserTests =
  map (Q.uncurry3 assertParses) $
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
                    (EMethod $
                     Method
                       "f"
                       [("x", TInt)]
                       (EAssign
                          { _lhs = EVar "x"
                          , _rhs = ETuple [EConst (VInt 1), EConst (VInt 2)]
                          })
                       Q.NormalMethod)
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
  , ( ", as separator"
    , "(<t> = e.foo()) , <1>"
    , ESeq
        (EAssign (ETuple [EVar "t"]) (ECall (EVar "e") "foo" []))
        (ETuple [EConst $ VInt 1]))
  , ( "& as seperator"
    , "(<t> = e.foo()) & <1>"
    , ECall
        (EConst VNil)
        "&"
        [ EAssign (ETuple [EVar "t"]) (ECall (EVar "e") "foo" [])
        , ETuple [EConst $ VInt 1]
        ])
  ]

invalidCases =
  map
    (uncurry (`doesntVerify` Q.nop))
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
    [ assertVerified "map comprehension to modify existing map" Q.nop $
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
    , assertVerified
        "assignment of tuple 4"
        ([prog'|
      method F(e) { new (const e=e) { method foo(m) { m & <t> = e.foo(m) }}}
      _e = adversary() |]) $
      [prog| F(F(_e)) |] ≈ [prog| F(F(_e)) |] : []
    , assertVerified
        "assignment of tuple 5"
        ([prog'|
      method F(e) { new (const e=e) { method foo() { <t> = e.foo() & <1> }}}
      _e = adversary() |]) $
      [prog| F(F(_e)) |] ≈ [prog| F(F(_e)) |] : []
    , assertVerified "assignment of tuple 6" ([prog'| 1 |]) $
      [prog| new () { method enc(m) { <t> = m }} |] ≈
      [prog| new () { method enc(m) { <t> = (<tg>=m & <tg>)  }} |] :
      []
    ]

bug :: Test
bug =
  assertVerifiedDebug "constant map comprehension" Q.nop $
  [prog| new() { method f() { ([x ↦ 1 | 1])[5] } } |] ≈
  [prog| new() { method f() { 1 } } |] :
  []

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
      (Q.emptyCtx {_ctxAllocStrategy = Q.Decrease})
      (Q.parseExpr "<new() {}, new() {}>")
      (VTuple [Sym {_symVal = Ref (-1)}, Sym {_symVal = Ref (-2)}])
  , assertEvalResult'
      "Decreasing allocation allows allocating objects in methods"
      Q.emptyCtxRHS
      [prog'|
(new() {
method f(x) { obj = (new() { method g(m) { 1 } }), obj.g(x) & 1 }
}).f(5)|]
      (VInt 1)
  , assertVerifyError
      "verification should detect extraneous methods on one side"
      Q.nop $
    [prog| new() { method f() { 1 } } |] ≈ [prog| new() { } |] : []
  , doesntVerify "if expression equivalence differing on one branch" Q.nop $
    [prog| new() { method f(x) { if (x) { 7 } else { 8 } } } |] ≈
    [prog| new() { method f(x) { if (x) { 7 } else { 9 } } } |] :
    []
  , assertVerified "<= works" Q.nop $
    [prog| new() { method f() { x <= x } } |] ≈
    [prog| new() { method f() { 1 } } |] :
    []
  , assertVerified "& well-behaved" Q.nop $
    [prog| new() { method f(x, y) { 1 & x & y & 1 } } |] ≈
    [prog| new() { method f(x, y) { 1 & y & x & 1 } } |] ≈
    [prog| new() { method f(x, y) { y & x & 1 } } |] :
    []
  , assertVerified "simple equality invariant" Q.nop $
    [prog| new (x=0) { method f() { <x, x> } } |] ≈
    Hint [fieldsEqual ["x"] ["y"]] :
    [prog| new (y=0) { method f() { <y, y> } } |] : []
  , assertVerified "simple const annotation" Q.nop $
    [prog| new (const x=0) { method f() { x } } |] ≈
    [prog| new (const x=0) { method f() { 0 } } |] :
    []
  , assertVerified "addition is commutative and 0 is identity" Q.nop $
    [prog| new () { method f(x, y) { 0 + x + 1 + y } } |] ≈
    [prog| new () { method f(x, y) { y + x + 1 } } |] :
    []
  , assertVerified "multiplication example" Q.nop $
    [prog| new () { method f(x, y) { x * 3 * y } } |] ≈
    [prog| new () { method f(x, y) { (x + x + x) * y } } |] ≈
    [prog| new () { method f(x, y) { x * (y + y + y) } } |] :
    []
  , assertVerified "arithmetic example" Q.nop $
    [prog| new () { method f(x:int, y, z) { x / 2 + y * z - x / 2 } } |] ≈
    [prog| new () { method f(x:int, y, z) { y * z } } |] :
    []
  , assertVerified "assignment to local variable" Q.nop $
    [prog|
new() {
  method f(x) { c = x & c }
} |] ≈
    [prog|
new() {
  method f(x) { x }
} |] :
    []
  , assertVerified "tupling never returns 0" Q.nop $
    [prog|
new() {
  method f(m) { <m> & 5 }
} |] ≈
    [prog|
new() {
  method f(m) { 5 }
}|] :
    []
  , assertVerified "if-else with symbolic condition" Q.nop $
    [prog| new () { method f(x) { if (x) { 5 } else { 6 } } } |] ≈
    [prog| new () { method f(x) { if (!x) { 6 } else { 5 } } } |] :
    []
  , assertVerified "if-else with same value in both branches" Q.nop $
    [prog| new () { method f() { if (x) 5 else 5 } } |] ≈
    [prog| new () { method f() { 5 } } |] :
    []
  , assertVerified "if-else with true guard" Q.nop $
    [prog| new () { method f() { if (1) 7 else 8 } } |] ≈
    [prog| new () { method f() { 7 } } |] :
    []
  , assertVerified "if-else with false guard" Q.nop $
    [prog| new() { method f() { if (2 < 1) 7 else 8 } } |] ≈
    [prog| new() { method f() { 8 } } |] :
    []
  , assertVerified "post-increment example 1" Q.nop $
    [prog| new () { method f() { x = 0 , x++ , x } } |] ≈
    [prog| new () { method f() { 1 } } |] :
    []
  , assertVerified "post-increment example 2" Q.nop $
    [prog| new () { method f(x) { x++ } } |] ≈
    [prog| new () { method f(x) { y = x , x = x + 1 , y } } |] :
    []
  , assertVerified "post-increment example 3" Q.nop $
    [prog| new () { method f() { x = 0 , x++ } } |] ≈
    [prog| new () { method f() { 0 } } |] :
    []
  , assertVerified "post-increment in a map index" Q.nop $
    [prog| new (m=0) { method f() { x = 0, m = 0, m[x++] = 42, m[0] } } |] ≈
    [prog| new () { method f() { 42 } } |] :
    []
  , assertVerified "less-than operator example" Q.nop $
    [prog| new () { method f(x:int, y:int) { !(x < y) | !(x == y) } } |] ≈
    [prog| new () { method f(x:int, y:int) { 1 } } |] :
    []
  , assertVerified "Z(..) is idempotent" Q.nop $
    [prog|
new() {
  method f(m) { Z(Z(m)) }
}|] ≈
    [prog|
new() {
  method f(m) { Z(m) }
}|] :
    []
  , assertVerified "call on symbolic object" Q.nop $
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
  , assertVerified "call on symbolic map value" Q.nop $
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
  , assertVerified "object maps with an invariant" Q.nop $
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
  , assertVerified "object maps with invariant using field access" Q.nop $
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
  , assertVerified "commute two new(){} expressions used in result" Q.nop $
    [prog|
new () { method f() { x = new() {}, y = new() {}, <x, y> } } |] ≈
    [prog|
new () { method f() { x = new() {}, y = new() {}, <y, x> } } |] :
    []
  , assertVerified
      "commute two new(){} expressions with an extra new on one side"
      Q.nop $
    [prog|
new () { method f() { new() {} } } |] ≈
    Hint [IgnoreCache] :
    [prog|
new () { method f() { x = new() {}, y = new() {}, if (x) { y } else { y } } }|] :
    []
  , assertVerified "reason about new()s used only in path condition" Q.nop $
    [prog|
new () { method f() { if (new(){}) { 5 } else { 6 } } }|] ≈
    Hint [IgnoreCache] :
    [prog|
new () { method f() { if (new(){}) { 5 } else { 6 } } }|] :
    []
  , assertVerified "syntactic sugar rnd() also commutes" Q.nop $
    [prog| new() { method f() { x = rnd(), y = rnd(), <x, y> } } |] ≈
    Hint [IgnoreCache] :
    [prog| new() { method f() { x = rnd(), y = rnd(), <y, x> } } |] : []
  , assertVerified "basic set literals and membership" Q.nop $
    [prog| new() { method f() { 1 ∈ {1} } } |] ≈
    [prog| new() { method f() { 1 } } |] :
    []
  , assertVerified "set membership in singleton set" Q.nop $
    [prog| new() { method f(x) { x ∈ {1} } } |] ≈
    [prog| new() { method f(x) { x == 1 } } |] :
    []
  , assertVerified "trivial set comprehension" Q.nop $
    [prog| new() { method f(y) { y ∈ {x | x ∈ {1}, 1} } } |] ≈
    [prog| new() { method f(y) { y == 1 } } |] :
    []
  , assertVerified "constant map comprehension" Q.nop $
    [prog| new() { method f() { ([x ↦ 1 | 1])[5] } } |] ≈
    [prog| new() { method f() { 1 } } |] :
    []
  , assertVerified "map comprehension with another map in predicate" Q.nop $
    [prog| new() { method f() { (m = map, m[1] = 42), ([x ↦ 42 | m[x]])[1] } } |] ≈
    [prog| new() { method f() { 42 } } |] :
    []
  , assertVerified
      "map comprehension using another map in predicate and mapping function"
      Q.nop $
    [prog| new() { method f() { (m = map, m[1] = 42), ([x ↦ m[x]+1 | m[x]])[1] } } |] ≈
    [prog| new() { method f() { 43 } } |] :
    []
  , assertVerified "⊆ operation on concrete values" Q.nop $
    [prog|
new() { method f() { m = 0, m[0] = 1, m[1] = 1, n = 0, n[0] = 1, n ⊆ m } } |] ≈
    [prog|
new() { method f() { 1 } } |] :
    []
  , assertVerified "⊆ operation on symbolic maps and indices" Q.nop $
    [prog|
new(m: map * *) { method f(x) { n = m, n[x] = 1, m ⊆ n } } |] ≈
    [prog|
new() { method f(x) { 1 } } |] :
    []
  , assertVerified "local method" Q.nop $
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
  , assertVerified "Pattern-matching behaves like tuple projection" Q.nop $
    [prog|
new() {
  method f(x) { <a, b> = x, <b, a> }
} |] ≈
    [prog|
new() {
  method f(x) { <x`1, x`0> }
}|] :
    []
  , assertVerified "Pattern-matching remembers tuple size" Q.nop $
    [prog|
new() {
  method f(x) { <a, b> = x, <a, b> }
}|] ≈
    [prog|
new() {
  method f(x) { x }
} |] :
    []
  , assertVerified "Nested symbolic objects" Q.nop $
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
  , assertVerified "Nested symbolic objects in maps" Q.nop $
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
  , assertVerified "Type declaration with constant initializer" Q.nop $
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
  , assertVerified "Dropping a call to rnd()" Q.nop $
    [prog|new() { x = rnd(), rnd() }|] ≈ [prog|new() { rnd() }|] : []
  , assertVerified "uninitialized nested map" Q.nop $
    [prog|
new() {
  method f(x, y) { a[x][y] = 5 & a[x][y] }
}|] ≈
    [prog|
new() {
  method f(x, y) { 5 }
}|] :
    []
  , assertVerified
      "assignment of tuple 1"
      ([prog'|
      method F(e) { new (const e=e) { method foo(m) { <t> = e.foo(m) }}}
      _e = adversary() |]) $
    [prog| F(F(_e)) |] ≈ [prog| F(F(_e)) |] : []
  , assertVerified
      "assignment of tuple 2"
      ([prog'|
      method F(e) { new (const e=e) { method foo(m) { 1 & <t> = e.foo(m) }}}
      _e = adversary() |]) $
    [prog| F(F(_e)) |] ≈ [prog| F(F(_e)) |] : []
  , assertVerified
      "assignment of tuple 3"
      ([prog'|
      method F(e) { new (const e=e) { method foo() { <t> = e.foo() , <1> }}}
      _e = adversary() |]) $
    [prog| F(F(_e)) |] ≈ [prog| F(F(_e)) |] : []
  ]

main :: IO ()
main = do
  args <- Environment.getArgs
  let t =
        case args of
          [] -> tests
          ["bug"] -> bug
          ["failing"] -> failingTests
          _ -> error "Illegal arguments"
  counts@Counts {cases, tried, errors, failures} <- T.runTestTT t
  if failures > 0 || errors > 0
    then error $ "Failed tests: " ++ show counts
    else if tried /= cases
           then error $ "Not all tests ran: " ++ show counts
           else return ()
