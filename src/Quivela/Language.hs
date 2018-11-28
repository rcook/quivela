-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}

module Quivela.Language
  ( Addr
  , AllocStrategy(..)
  , Context(..)
  , Diff(..)
  , Expr(..)
  , Field(..)
  , FunDecl(..)
  , Local(..)
  , Method(..)
  , MethodKind(..)
  , Object(..)
  , PathCond
  , Place(..)
  , Proof
  , ProofHint(..)
  , ProofPart(..)
  , Prop(..)
  , SymValue(..)
  , Type(..)
  , Value(..)
  , pattern VRef
  , Var
  , comprPred
  , comprValue
  , comprVar
  , conjunction
  , ctxAdvCalls
  , ctxAllocStrategy
  , ctxAssumptions
  , ctxFunDecls
  , ctxObjs
  , ctxScope
  , ctxThis
  , ctxTypeDecls
  , efunDeclArgs
  , efunDeclName
  , emethodName
  , emptyCtx
  , emptyCtxRHS
  , fieldInit
  , fieldName
  , fieldType
  , funDeclArgs
  , funDeclName
  , immutable
  , localImmutable
  , localType
  , localValue
  , methodBody
  , methodFormals
  , methodKind
  , methodName
  , newBody
  , newFields
  , nop
  , objAdversary
  , objLocals
  , objMethods
  , objType
  , placeConst
  , placeLens
  , placeType
  , symVal
  , typedeclBody
  , typedeclFormals
  , typedeclValues
  , valMap
  , varBindings
  ) where

import Control.Applicative ((<$>))
import Control.Arrow (second)
import qualified Control.Lens as C
import Control.Lens ((^.), set)
import Data.Data (Data)
import qualified Data.Map as M
import Data.Serialize (Serialize, get)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

{- Lenses

Since interpreting quivela programs uses a lot of nested records, we use
the lens library to read and write inside nested records. A lens can
be thought of a combined getter and setter than can be passed around
as a first-class value and also extends to reading and writing inside
Maps.

See https://github.com/ekmett/lens/wiki for details.
-}
type Addr = Integer

type Var = String

type Scope = M.Map Var (Value, Type)

type Env = M.Map Var Value

data Type
  = TInt
  | TTuple [Type]
  | TMap Type
         Type
  | TAny
  | TNamed String
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | Symbolic values representing unknowns and operations on the
-- Calls to the adversary are also symbolic.
data SymValue
  = SymVar String
           Type
  | Insert Value
           Value
           Value
  | Proj Value
         Value
  | Lookup Value
           Value
  | AdversaryCall [[Value]]
  | Add Value
        Value
  | Sub Value
        Value
  | Mul Value
        Value
  | Div Value
        Value
  | Lt Value
       Value
  | Le Value
       Value
  | SetCompr Value
             Var
             Prop
  | ITE Prop
        Value
        Value
  | MapCompr Var
             Value
             Prop
  | In Value
       Value
  | Union Value
          Value
  | MapUnion Value
             Value
  | Intersect Value
              Value
  | Submap Value
           Value
  | SymRef String -- FIXME: check if we can remove these and use refs for everything
  | Ref Addr
  | Deref Value
          String
  | Z Value
  | Call String
         [Value] -- ^ Calls to declared, but not defined, functions
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- Since we pattern-match repeatedly on references in various places, we define
-- a pattern synonym that handles the fact that references are actually symbolic
pattern VRef a = Sym (Ref a)

-- | Quivela values
data Value
  = VInt Integer
  | VMap { _valMap :: M.Map Value Value }
  | VTuple [Value]
  | VNil
  | VSet { _valSet :: S.Set Value }
  | Sym { _symVal :: SymValue }
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | Data type for field initializers
data Field = Field
  { _fieldName :: String
  , _fieldInit :: Expr -- ^ Expression to initialize the field with
  , _fieldType :: Type
  , _immutable :: Bool -- ^ Is the field constant?
  } deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

data MethodKind
  = NormalMethod
  | LocalMethod
  | Invariant
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

data Expr
  = ENop
  | EAssign { _lhs :: Expr
            , _rhs :: Expr }
  | EVar Var
  | EConst Value
  | EProj Expr
          Var
  | EIdx Expr
         Expr
  | ENew { _newFields :: [Field]
         , _newBody :: Expr }
  | ENewConstr { _newConstrName :: String
               , _newConstrArgs :: [(Var, Expr)] }
  | EMethod { _emethodName :: String
            , _emethodArgs :: [(String, Type)]
            , _emethodBody :: Expr
            , _emethodKind :: MethodKind }
  | ECall { _callObj :: Expr
          , _callName :: String
          , _callArgs :: [Expr] }
  | ETuple [Expr]
  | ETupleProj Expr
               Expr
  | ESeq Expr
         Expr
  | EIf Expr
        Expr
        Expr
  | EIn Expr
        Expr
  | ESubmap Expr
            Expr
  | EUnion Expr
           Expr
  | EIntersect Expr
               Expr
  | ETypeDecl { _typedeclName :: String
              , _typedeclFormals :: [(Var, Bool, Type)]
              , _typedeclValues :: [(Var, Value)]
              , _typedeclBody :: Expr }
  | ESetCompr { _comprVar :: Var
              , _comprValue :: Expr
              , _comprPred :: Expr -- set comprehensions
               }
  | EMapCompr { _comprVar :: Var
              , _comprValue :: Expr
              , _comprPred :: Expr -- map comprehensions
               }
  | EAssume Expr
            Expr
  | EFunDecl { _efunDeclName :: String
             , _efunDeclArgs :: [Var] -- uninterpreted functions
              }
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

instance Serialize SymValue

instance Serialize Value

instance Serialize Type

instance Serialize Field

instance Serialize MethodKind

instance Serialize Expr

instance Serialize Prop

-- | The value of a field of an object in the heap
data Local = Local
  { _localValue :: Value
  , _localType :: Type
  , _localImmutable :: Bool
  } deriving (Eq, Read, Show, Ord, Data, Typeable)

data Method = Method
  { _methodName :: String
  , _methodFormals :: [(String, Type)]
  , _methodBody :: Expr
  , _methodKind :: MethodKind
  } deriving (Eq, Read, Show, Ord, Data, Typeable)

data Object = Object
  { _objLocals :: M.Map Var Local
  , _objMethods :: M.Map Var Method
  , _objType :: Type
                     -- ^ Type of the object if it was constructed with a named type constructor
  , _objAdversary :: Bool -- ^ Is the object an adversary?
  } deriving (Eq, Read, Show, Ord, Data, Typeable)

-- | Named types are identifiers of more complex types whose semantics are given
-- as Haskell expressions.
type TypeName = String

-- | To make our lives easier reasoning about equivalences that require
-- new to be commutative, we would like the address identifiers used on the left-hand
-- side and the right-hand side to be disjoint. We implement this by using negative
-- numbers for addresses on the right-hand side and positive numbers otherwise. This
-- datatype encodes which allocation scheme to use.
data AllocStrategy
  = Increase
  | Decrease
  deriving (Eq, Read, Show, Ord, Data, Typeable)

data Context = Context
  { _ctxObjs :: M.Map Addr Object
  , _ctxThis :: Addr
  , _ctxScope :: Scope -- ^ Keeps track of local variables and arguments in a
                                            -- method call.
  , _ctxAdvCalls :: [[Value]] -- ^ All adversary calls so far
  , _ctxTypeDecls :: M.Map Var Expr
                       -- ^ Map from type names to typedecl expressions (all values in this
                       -- map can be assumed to be of the form (ETypeDecl ...)
  , _ctxAllocStrategy :: AllocStrategy
  , _ctxAssumptions :: [(Expr, Expr)]
  , _ctxFunDecls :: M.Map String FunDecl
  } deriving (Eq, Read, Show, Ord, Data, Typeable)

data FunDecl = FunDecl
  { _funDeclName :: String
  , _funDeclArgs :: [Var]
  } deriving (Eq, Read, Show, Ord, Data, Typeable)

data Place = Place
  { _placeLens :: (forall f. Applicative f =>
                               ((Value -> f Value) -> Context -> f Context))
  , _placeConst :: Bool
  , _placeType :: Type
  }

-- | Propositions. These are used both to keep track of the path condition
-- as well as for the verification conditions we generate later on.
data Prop
  = Value :=: Value
  | Not Prop
  | Forall [(Var, Type)]
           Prop
  | Prop :=>: Prop
  | Prop :&: Prop
  | PTrue
  | PFalse
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

conjunction :: [Prop] -> Prop
conjunction [] = PTrue
conjunction [p] = p
conjunction ps = foldr1 (:&:) ps

-- | A path condition is a list of propositions that all hold on a given path
-- These could be stored as just one big conjunction instead, but representing
-- them as a list simplifies reasoning about which paths are prefixes of others.
type PathCond = [Prop]

data Binding = Binding
  { _bindingName :: Var
  , _bindingConst :: Bool
  } deriving (Eq, Ord, Show, Read)

-- | Proof hints. These include relational invariants, use of assumptions
-- and controlling convenience features such as automatic inference of relational
-- equalities.
data ProofHint
  = EqualInv (Addr -> Context -> Value)
             (Addr -> Context -> Value)
  -- ^ Equality of a value from the LHS and RHS contexts
  | Rewrite Expr
            Expr
  | NoInfer -- ^ turn off proof hint inference for this step
  | IgnoreCache -- ^ Don't use verification cache when checking this step
  | Admit
  -- ^ Don't check this step
  | NoAddressBijection -- ^ Don't try to remap addresses and instead hope that they get allocated in the same order
  | UseAddressBijection (M.Map Addr Addr) -- ^ Start from explicit bijection of addresses
  | Note String
  deriving (Generic)

data Diff
  = NewField Field
  | DeleteField Var
  | OverrideMethod Expr -- assumes expr is an EMethod
  | DeleteMethod Var
  deriving (Read, Show, Eq, Ord)

-- | One part of a quivela proof, which is either an expression, or a proof hint.
-- An followed by a hint and another expression is verified using that hint,
-- while two expressions in a row are verified without additional proof hints.
-- The steps are chained automatically, e.g. @[e1, h1, e2, e3]@ will result in verifying
-- @e1 ~[h1] e2 ~ e3@
data ProofPart
  = Prog Expr
  | PDiff [Diff]
  | Hint [ProofHint]

type Proof = [ProofPart]

instance Show ProofPart where
  show (Prog e) = "Program:\n" ++ show e
  show (PDiff d) = "Diff:\n" ++ show d
  show _ = "<invariant>"

concat <$>
  mapM
    C.makeLenses
    [ ''Method
    , ''Object
    , ''Context
    , ''Place
    , ''FunDecl
    , ''Binding
    , ''Local
    , ''Field
    , ''Expr
    , ''Value
    ]

-- | Returns a set of free variables in the expression and a set of bound identifiers
-- that may be bound by execution of the expression. Note that some executions may not
-- actually bind all variables in the second set.
--
-- Note that computing free variables is complicated by the fact that assignments
-- to non-existent variables bind the variables in the "rest" of the expression,
-- where the rest can be siblings of the assignment to the right in the AST
varBindings :: Expr -> (S.Set Var, S.Set Binding)
varBindings ENop = (S.empty, S.empty)
varBindings (EVar x) = (S.singleton x, S.empty)
varBindings (EConst _) = (S.empty, S.empty)
varBindings (EAssign (EVar x) rhs)
  | (freeRhs, boundRhs) <- varBindings rhs =
    ( freeRhs
    , S.insert (Binding {_bindingName = x, _bindingConst = False}) boundRhs)
varBindings (EAssign lhs rhs) = varBindings lhs `bindingSeq` varBindings rhs
varBindings (ESeq e1 e2) = varBindings e1 `bindingSeq` varBindings e2
varBindings (ECall obj name args) =
  let (freeObj, boundObj) = varBindings obj
   in varBindingsList (freeObj, boundObj) args
-- Note that anything assigned to in the body will end in a local scope of the object,
-- so the body cannot introduce new bound variables
varBindings (ENew fields body) =
  let (fieldsFree, fieldsBound) =
        varBindingsList (S.empty, S.empty) $ map (^. fieldInit) fields
      (bodyFree, bodyBound) = varBindings body
   in ( bodyFree `S.difference`
        (S.fromList (map (^. fieldName) fields) `S.union`
         S.map (^. bindingName) fieldsBound)
      , fieldsBound)
varBindings (EProj eobj name) = varBindings eobj
varBindings (EIdx base idx) = varBindings base `bindingSeq` varBindings idx
  -- Variables bound inside a method body are not visible outside:
varBindings (EMethod name args body isInv) =
  let (bodyFree, bodyBound) = varBindings body
   in (bodyFree `S.difference` S.fromList (map fst args), S.empty)
varBindings (ETuple elts) = varBindingsList (S.empty, S.empty) elts
varBindings (ETupleProj base idx) =
  varBindings base `bindingSeq` varBindings idx
varBindings (ETypeDecl name formals values body) =
  varBindings
    (ENew
       (map
          (\(name, immut, typ) ->
             Field
               { _fieldName = name
               , _fieldType = typ
               , _fieldInit = ENop
               , _immutable = immut
               })
          formals ++
        map
          (\(name, value) ->
             Field
               { _fieldName = name
               , _fieldType = TAny
               , _fieldInit = EConst value
               , _immutable = False
               })
          values)
       body)
varBindings (ENewConstr name values) =
  varBindingsList (S.empty, S.empty) (map snd values)
varBindings (EIf cnd thn els) =
  varBindings cnd `bindingSeq`
  (let (thnFree, thnBound) = varBindings thn
       (elsFree, elsBound) = varBindings els
    in (thnFree `S.union` elsFree, thnBound `S.union` elsBound))

-- | Combine two pieces of binding information assuming that the second set of bindings
-- is produced by an expression that will be evaluated after the first
bindingSeq ::
     (S.Set Var, S.Set Binding)
  -> (S.Set Var, S.Set Binding)
  -> (S.Set Var, S.Set Binding)
bindingSeq (free1, bound1) (free2, bound2) =
  ( free1 `S.union` (free2 `S.difference` S.map (^. bindingName) bound1)
  , bound1 `S.union` bound2)

-- | Folds 'varBindings' over a list of expressions with a given set of initial bindings
varBindingsList ::
     (S.Set Var, S.Set Binding) -> [Expr] -> (S.Set Var, S.Set Binding)
varBindingsList init exprs =
  foldl
    (\(freeAcc, boundAcc) expr ->
       let (freeExpr, boundExpr) = varBindings expr
        in ( (freeAcc `S.union` freeExpr) `S.difference`
             S.map (^. bindingName) boundAcc
           , boundAcc `S.union` boundExpr))
    init
    exprs

emptyCtx :: Context
emptyCtx =
  Context
    { _ctxObjs =
        M.fromList
          [ ( 0
            , Object
                { _objLocals = M.empty
                , _objMethods = M.empty
                , _objType = TAny
                , _objAdversary = False
                })
          ]
    , _ctxThis = 0
    , _ctxAdvCalls = []
    , _ctxScope = M.empty
    , _ctxTypeDecls = M.empty
    , _ctxAllocStrategy = Increase
    , _ctxAssumptions = []
    , _ctxFunDecls = M.empty
    }

emptyCtxRHS :: Context
emptyCtxRHS = set ctxAllocStrategy Decrease emptyCtx

nop :: Expr
nop = ENop
