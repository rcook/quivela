-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}

import qualified Control.DeepSeq as DS
import Control.Exception (SomeException, catch)
import qualified Data.Map as M
import qualified Test.HUnit as T
import Test.HUnit (Assertion, Test(TestCase, TestList))

import qualified Quivela.Examples as E
import qualified Quivela.Language as L
import Quivela.Language
  ( Context(..)
  , Expr(..)
  , Proof(..)
  , SymValue(..)
  , Type(..)
  , Value(..)
  , nop
  )
import qualified Quivela.Parse as P
import qualified Quivela.QuasiQuote as Q
import qualified Quivela.SymEval as S
import qualified Quivela.Util as U
import qualified Quivela.Verify as V

-- Don't print garbage during tests.  If a test fails, debug it separately.
noDebugEnv = S.emptyVerifyEnv { S._debugFlag = False } 

assertVerified :: String -> Expr -> Proof -> Assertion
assertVerified msg prefix proof = do
  V.clearCache
  res <- Q.prove' noDebugEnv prefix proof
  T.assertEqual msg 0 res

assertError :: String -> IO a -> Assertion
assertError msg x = do
  errored <- fmap DS.force $ catch (x >> pure False) handler
  if not errored
    then T.assertFailure $ "Should have failed: " ++ msg
    else T.assertBool "true" True
  where
    handler :: SomeException -> IO Bool
    handler _ = do
      pure True

assertEvalError :: String -> Expr -> Assertion
assertEvalError msg e =
  assertError msg . V.runVerify noDebugEnv $ S.symEval (e, L.emptyCtx, [])

assertEvalResult' :: String -> Context -> Expr -> Value -> Assertion
assertEvalResult' msg ctx e v = do
  (res, _, _) <-
    S.singleResult <$> (V.runVerify noDebugEnv $ (S.symEval (e, ctx, [])))
  T.assertEqual msg res v

assertEvalResult :: String -> Expr -> Value -> Assertion
assertEvalResult msg e v = assertEvalResult' msg L.emptyCtx e v

assertVerifyError :: String -> Expr -> Proof -> Assertion
assertVerifyError msg prefix proof =
  assertError msg $ Q.prove' noDebugEnv prefix proof

assertParses :: String -> String -> Expr -> Assertion
assertParses msg progText e = T.assertEqual msg (P.parseExpr progText) e

doesntVerify :: String -> Expr -> Proof -> Assertion
doesntVerify msg prefix proof = do
  remaining <- Q.prove' noDebugEnv prefix proof
  T.assertBool msg (remaining > 0)

parserTests =
  map (TestCase . U.uncurry3 assertParses) $
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

tests :: Test
tests =
  TestList $
  parserTests ++
  invalidCases ++
  [ TestCase $ assertEvalError "assigning to constant variable" E.assignConst
  , TestCase $ assertEvalError "assigning to constant variable" E.assignConst'
  , TestCase $
    assertEvalError
      "assigning to constant field in typedecl'd object"
      E.assignConstTypeDecl
  , TestCase $
    assertEvalError "ill-typed assignment to object field" E.illTypedAssign
  , TestCase $
    assertEvalError "ill-typed assignment to object field" E.illTypedAssign'
  , TestCase $
    assertEvalError
      "ill-typed assignment to method parameter"
      E.illTypedParamAssign
  , TestCase $
    assertEvalError
      "ill-typed assignment using object type"
      E.illTypedConstrAssign
  , TestCase $
    assertEvalError "ill-typed object creation" E.illTypedObjectCreation
  , TestCase $
    assertEvalError
      "ill-typed object creation using constructor"
      E.illTypedObjectCreationNamed
  , TestCase $
    assertEvalResult
      "multiple indexing expressions in sequence"
      E.doubleIdx
      (VInt 5)
  , TestCase $
    assertEvalResult "nested object field lookups" E.doubleFieldDeref (VInt 5)
  , TestCase $
    assertEvalResult
      "post-increment on object field"
      E.incrementFieldDeref
      (VTuple [VInt 1, VInt 2])
  , TestCase $
    assertEvalResult "type declarations with parameters" E.typedeclTest (VInt 5)
  , TestCase $
    assertEvalResult
      "Addresses can be used as symbolic values"
      E.addressesSymbolic
      (Sym (Add (Sym (Ref 1)) (Sym (Ref 2))))
  , TestCase $
    assertEvalResult'
      "Decreasing allocation strategy should yield negative addresses"
      (L.emptyCtx {_ctxAllocStrategy = L.Decrease})
      (P.parseExpr "<new() {}, new() {}>")
      (VTuple [Sym {_symVal = Ref (-1)}, Sym {_symVal = Ref (-2)}])
  , TestCase $
    assertEvalResult'
      "Decreasing allocation allows allocating objects in methods"
      L.emptyCtxRHS
      E.decreaseAlloc
      (VInt 1)
  , TestCase $
    assertVerifyError
      "verification should detect extraneous methods on one side"
      nop
      E.extraMethodsTest
  , TestCase $
    doesntVerify
      "if expression equivalence differing on one branch"
      nop
      E.ifEqvFalse
  , TestCase $ assertVerified "<= works" nop E.leTaut
  , TestCase $ assertVerified "& well-behaved" nop E.andExample
  , TestCase $ assertVerified "simple equality invariant" nop E.eqInvExample
  , TestCase $ assertVerified "simple const annotation" nop E.constExample
  , TestCase $
    assertVerified "addition is commutative and 0 is identity" nop E.addExample
  , TestCase $ assertVerified "multiplication example" nop E.mulExample
  , TestCase $ assertVerified "arithmetic example" nop E.arithExample
  , TestCase $ assertVerified "assignment to local variable" nop E.assignAnd
  , TestCase $ assertVerified "tupling never returns 0" nop E.tuplingAnd
  , TestCase $ assertVerified "if-else with symbolic condition" nop E.ifSymbolic
  , TestCase $
    assertVerified "if-else with same value in both branches" nop E.ifSimp
  , TestCase $ assertVerified "if-else with true guard" nop E.ifConcreteTrue
  , TestCase $ assertVerified "if-else with false guard" nop E.ifConcreteFalse
  , TestCase $ assertVerified "post-increment example 1" nop E.postIncrExample3
  , TestCase $ assertVerified "post-increment example 2" nop E.postIncrExample2
  , TestCase $ assertVerified "post-increment example 3" nop E.postIncrExample1
  , TestCase $
    assertVerified "post-increment in a map index" nop E.postIncrementInMap
  , TestCase $ assertVerified "less-than operator example" nop E.leExample
  , TestCase $ assertVerified "Z(..) is idempotent" nop E.zIdempotent
  , TestCase $ assertVerified "call on symbolic object" nop E.symcallTest
  , TestCase $ assertVerified "call on symbolic map value" nop E.symcallMap
  , TestCase $
    assertVerified "object maps with an invariant" nop E.symcallMapParam
  , TestCase $
    assertVerified
      "object maps with invariant using field access"
      nop
      E.mapInvariantField
  , TestCase $
    assertVerified
      "commute two new(){} expressions used in result"
      nop
      E.commuteNews
  , TestCase $
    assertVerified
      "commute two new(){} expressions with an extra new on one side"
      nop
      E.commuteNewPathCondition
  , TestCase $
    assertVerified
      "reason about new()s used only in path condition"
      nop
      E.commuteNewContradictoryPath
  , TestCase $
    assertVerified "syntactic sugar rnd() also commutes" nop E.commuteRands
  , TestCase $
    assertVerified "basic set literals and membership" nop E.setInTest
  , TestCase $ assertVerified "set membership in singleton set" nop E.setInTest2
  , TestCase $ assertVerified "trivial set comprehension" nop E.setComprTest1
  , TestCase $ assertVerified "constant map comprehension" nop E.mapComprTest1
  , TestCase $
    assertVerified
      "map comprehension with another map in predicate"
      nop
      E.mapComprTest2
  , TestCase $
    assertVerified
      "map comprehension using another map in predicate and mapping function"
      nop
      E.mapComprTest3
  -- , TestCase $ assertVerified "map comprehension to modify existing map" nop mapComprTest4
  , TestCase $ assertVerified "⊆ operation on concrete values" nop E.constSubmap
  , TestCase $
    assertVerified "⊆ operation on symbolic maps and indices" nop E.paramSubmap
  , TestCase $ assertVerified "local method" nop E.localMethodExample
  , TestCase $
    assertVerified
      "Pattern-matching behaves like tuple projection"
      nop
      E.patMatch1
  , TestCase $
    assertVerified "Pattern-matching remembers tuple size" nop E.patMatch2
  , TestCase $ assertVerified "Nested symbolic objects" nop E.nestedObjs
  , TestCase $
    assertVerified "Nested symbolic objects in maps" nop E.nestedObjMap
  , TestCase $
    uncurry
      (assertVerified "calling uninterpreted function with same arguments")
      E.fundeclTest1
  , TestCase $
    uncurry
      (doesntVerify "uninterpreted function called with different arguments")
      E.fundeclTest2
  , TestCase $
    assertVerified
      "Type declaration with constant initializer"
      nop
      E.typedeclConstField
  , TestCase $
    uncurry
      (assertVerified "Placing object and its parameter in different maps")
      E.objectInTwoMaps
  , TestCase $
    uncurry
      (assertVerified "Placing object and its parameter in different maps (2)")
      E.objectInTwoMaps'
  , TestCase $ assertVerified "Dropping a call to rnd()" nop E.dropRandom
  ]
  where
    invalidCases =
      map
        (TestCase . uncurry (`doesntVerify` nop))
        [ ("trivial contradiction", E.incorrectVerify1)
        , ("incorrect arithmetic", E.incorrectVerify2)
        , ( "variable capture in method inlining"
          , E.incorrectMethodInlineCapture)
        ]

main :: IO ()
main = T.runTestTT tests >> return ()
