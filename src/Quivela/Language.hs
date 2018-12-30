-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Quivela.Language
  ( Addr
  , AllocStrategy(..)
  , Config
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
  , Result
  , Results
  , SymValue(..)
  , Type(..)
  , Value(..)
  , pattern VRef
  , Var
  , bindingConst
  , callArgs
  , callName
  , callObj
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
  , emethodArgs
  , emethodBody
  , emethodKind
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
  , lhs
  , methodBody
  , methodFormals
  , methodKind
  , methodName
  , newBody
  , newConstrArgs
  , newConstrName
  , newFields
  , nop
  , objAdversary
  , objLocals
  , objMethods
  , objType
  , placeConst
  , placeLens
  , placeType
  , rhs
  , symVal
  , typedeclBody
  , typedeclFormals
  , typedeclName
  , typedeclValues
  , valMap
  , valSet
  , varBindings
  ) where

import qualified Control.Lens as Lens
import Control.Lens ((<&>), (^.))
import qualified Control.Monad as Monad
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Quivela.Prelude
import Quivela.Util(PartialEq(..))

type Addr = Integer

type Var = String

type Scope = Map Var (Value, Type)

data Type
  = TInt
  | TTuple [Type]
  | TMap Type
         Type
  | TAny
  | TSet Type
  | TNamed String
  deriving (Eq, Show, Ord, Data, Generic)

instance Serialize Type

-- | Symbolic values representing unknowns and operations on them
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
  deriving (Eq, Show, Ord, Data, Generic)

instance Serialize SymValue

-- Define how to insert into a symbolic value via a lens:
type instance Lens.Index SymValue = Value

type instance Lens.IxValue SymValue = Value

instance Lens.Ixed SymValue where
  ix k f m = f (Sym $ Lookup k (Sym m)) <&> \v' -> Insert k v' (Sym m)

-- | Quivela values
data Value
  = VInt Integer
  | VMap { _valMap :: Map Value Value }
  | VTuple [Value]
  | VNil
  | VSet { _valSet :: Set Value }
  | Sym { _symVal :: SymValue }
  deriving (Eq, Show, Ord, Data, Generic)

instance Serialize Value

-- Since we pattern-match repeatedly on references in various places, we define
-- a pattern synonym that handles the fact that references are actually symbolic
pattern VRef :: Addr -> Value

pattern VRef a = Sym (Ref a)

-- | Data type for field initializers
data Field = Field
  { _fieldName :: String
  , _fieldInit :: Expr -- ^ Expression to initialize the field with
  , _fieldType :: Type
  , _immutable :: Bool -- ^ Is the field constant?
  } deriving (Eq, Show, Ord, Data, Generic)

instance Serialize Field

data MethodKind
  = NormalMethod
  | LocalMethod
  | Invariant
  deriving (Eq, Show, Ord, Data, Generic)

instance Serialize MethodKind

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
  -- { x + 1 | x ∈ y ∪ z, g(x) > f(x) }
  | ESetCompr { _comprVar :: Var
              , _comprValue :: Expr
              , _comprPred :: Expr -- set comprehensions
               }
  -- [ x ↦ h(x, y) | x ∈ y ∪ z, g(x) > f(x) ]
  | EMapCompr { _comprVar :: Var
              , _comprValue :: Expr
              , _comprPred :: Expr -- map comprehensions
               }
  | EAssume Expr
            Expr
  | EFunDecl { _efunDeclName :: String
             , _efunDeclArgs :: [Var] -- uninterpreted functions
              }
  deriving (Eq, Show, Ord, Data, Generic)

instance Serialize Expr

nop :: Expr
nop = ENop

-- | The value of a field of an object in the heap
data Local = Local
  { _localValue :: Value
  , _localType :: Type
  , _localImmutable :: Bool
  } deriving (Eq, Show, Ord, Data)

data Method = Method
  { _methodName :: String
  , _methodFormals :: [(String, Type)]
  , _methodBody :: Expr
  , _methodKind :: MethodKind
  } deriving (Eq, Show, Ord, Data)

data Object = Object
  { _objLocals :: Map Var Local
  , _objMethods :: Map Var Method
  , _objType :: Type
                     -- ^ Type of the object if it was constructed with a named type constructor
  , _objAdversary :: Bool -- ^ Is the object an adversary?
  } deriving (Eq, Show, Ord, Data)

-- | To make our lives easier reasoning about equivalences that require
-- new to be commutative, we would like the address identifiers used on the left-hand
-- side and the right-hand side to be disjoint. We implement this by using negative
-- numbers for addresses on the right-hand side and positive numbers otherwise. This
-- datatype encodes which allocation scheme to use.
data AllocStrategy
  = Increase
  | Decrease
  deriving (Eq, Show, Ord, Data)

data Context = Context
  { _ctxObjs :: Map Addr Object
  , _ctxThis :: Addr
  , _ctxScope :: Scope
    -- ^ Keeps track of local variables and arguments in a method call.
  , _ctxAdvCalls :: [[Value]]
    -- ^ All adversary calls so far
  , _ctxTypeDecls :: Map Var Expr
    -- ^ Map from type names to typedecl expressions (all values in this
    -- map can be assumed to be of the form (ETypeDecl ...)
  , _ctxAllocStrategy :: AllocStrategy
  , _ctxAssumptions :: [(Expr, Expr)]
  , _ctxFunDecls :: Map String FunDecl
  } deriving (Eq, Show, Ord, Data)

data FunDecl = FunDecl
  { _funDeclName :: String
  , _funDeclArgs :: [Var]
  } deriving (Eq, Show, Ord, Data)

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
  deriving (Eq, Show, Ord, Data, Generic)

instance Serialize Prop

conjunction :: [Prop] -> Prop
conjunction [] = PTrue
conjunction [p] = p
conjunction ps = L.foldr1 (:&:) ps

-- | A path condition is a list of propositions that all hold on a given path
-- These could be stored as just one big conjunction instead, but representing
-- them as a list simplifies reasoning about which paths are prefixes of others.
type PathCond = [Prop]

data Binding = Binding
  { _bindingName :: Var
  , _bindingConst :: Bool
  } deriving (Eq, Ord, Show)

-- | Proof hints. These include relational invariants, use of assumptions
-- and controlling convenience features such as automatic inference of relational
-- equalities.
data ProofHint
  = EqualInv (Addr -> Context -> Value)
             (Addr -> Context -> Value)
  -- ^ Equality of a value from the LHS and RHS contexts
  | Rewrite Expr
            Expr
  | NoInfer
  -- ^ turn off proof hint inference for this step
  | IgnoreCache
  -- ^ Don't use verification cache when checking this step
  | Admit
  -- ^ Don't check this step
  | NoAddressBijection
  -- ^ Don't try to remap addresses and instead hope that they get allocated in the same order
  | UseAddressBijection (Map Addr Addr)
  -- ^ Start from explicit bijection of addresses
  | Note String
  deriving (Generic)

instance PartialEq ProofHint where
  NoInfer === NoInfer = Just True
  NoInfer === _ = Just False
  _ === NoInfer = Just False
  Rewrite e1 e2 === Rewrite e1' e2' = Just (e1 == e1' && e2 == e2')
  Rewrite _ _ === _ = Just False
  Admit === Admit = Just True
  Admit === _ = Just False
  EqualInv _ _ === EqualInv _ _ = Nothing
  EqualInv _ _ === _ = Just False
  IgnoreCache === IgnoreCache = Just True
  IgnoreCache === _ = Just False
  Note s === Note s' = Just (s == s')
  Note _ === _ = Just False
  NoAddressBijection === NoAddressBijection = Just True
  NoAddressBijection === _ = Just False
  UseAddressBijection m === UseAddressBijection m' = Just (m == m')
  UseAddressBijection _ === _ = Just False

data Diff
  = NewField Field
  | DeleteField Var
  | OverrideMethod Expr -- assumes expr is an EMethod
  | DeleteMethod Var
  deriving (Show, Eq, Ord)

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

L.concat <$>
  Monad.mapM
    Lens.makeLenses
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
varBindings :: Expr -> (Set Var, Set Binding)
varBindings ENop = (S.empty, S.empty)
varBindings (EFunDecl _ _) = (S.empty, S.empty)
varBindings (EAssume e1 e2) = combine e1 e2
varBindings (EVar x) = (S.singleton x, S.empty)
varBindings (EConst _) = (S.empty, S.empty)
varBindings (EAssign (EVar x) eRhs) =
  let (freeRhs, boundRhs) = varBindings eRhs
   in ( freeRhs
      , S.insert (Binding {_bindingName = x, _bindingConst = False}) boundRhs)
varBindings (EAssign eLhs eRhs) = varBindings eLhs `bindingSeq` varBindings eRhs
varBindings (ESeq e1 e2) = combine e1 e2
varBindings (EIn e1 e2) = combine e1 e2
varBindings (EUnion e1 e2) = combine e1 e2
varBindings (EIntersect e1 e2) = combine e1 e2
varBindings (ESubmap e1 e2) = combine e1 e2
varBindings (ESetCompr x v p) =
  let (free, bound) = combine v p
   in (S.delete x free, bound) -- TODO: should we remove bindings for `x` from `bound`?
varBindings (EMapCompr x v p) =
  let (free, bound) = combine v p
   in (S.delete x free, bound) -- TODO: should we remove bindings for `x` from `bound`?
varBindings (ECall obj _name args) =
  let (freeObj, boundObj) = varBindings obj
   in varBindingsList (freeObj, boundObj) args
-- Note that anything assigned to in the body will end in a local scope of the object,
-- so the body cannot introduce new bound variables
varBindings (ENew fields body) =
  let (_fieldsFree, fieldsBound) =
        varBindingsList (S.empty, S.empty) $ fmap (^. fieldInit) fields
      (bodyFree, _bodyBound) = varBindings body
   in ( bodyFree `S.difference`
        (S.fromList (fmap (^. fieldName) fields) `S.union`
         S.map (^. bindingName) fieldsBound)
      , fieldsBound)
varBindings (EProj eobj _name) = varBindings eobj
varBindings (EIdx base idx) = varBindings base `bindingSeq` varBindings idx
  -- Variables bound inside a method body are not visible outside:
varBindings (EMethod _name args body _isInv) =
  let (bodyFree, _bodyBound) = varBindings body
   in (bodyFree `S.difference` S.fromList (fmap fst args), S.empty)
varBindings (ETuple elts) = varBindingsList (S.empty, S.empty) elts
varBindings (ETupleProj base idx) =
  varBindings base `bindingSeq` varBindings idx
varBindings (ETypeDecl _name formals values body) =
  varBindings
    (ENew
       (fmap
          (\(name, immut, typ) ->
             Field
               { _fieldName = name
               , _fieldType = typ
               , _fieldInit = ENop
               , _immutable = immut
               })
          formals ++
        fmap
          (\(name, value) ->
             Field
               { _fieldName = name
               , _fieldType = TAny
               , _fieldInit = EConst value
               , _immutable = False
               })
          values)
       body)
varBindings (ENewConstr _name values) =
  varBindingsList (S.empty, S.empty) (fmap snd values)
varBindings (EIf cnd thn els) =
  varBindings cnd `bindingSeq`
  (let (thnFree, thnBound) = varBindings thn
       (elsFree, elsBound) = varBindings els
    in (thnFree `S.union` elsFree, thnBound `S.union` elsBound))

combine :: Expr -> Expr -> (Set Var, Set Binding)
combine e1 e2 = varBindings e1 `bindingSeq` varBindings e2

-- | Combine two pieces of binding information assuming that the second set of bindings
-- is produced by an expression that will be evaluated after the first
bindingSeq ::
     (Set Var, Set Binding) -> (Set Var, Set Binding) -> (Set Var, Set Binding)
bindingSeq (free1, bound1) (free2, bound2) =
  ( free1 `S.union` (free2 `S.difference` S.map (^. bindingName) bound1)
  , bound1 `S.union` bound2)

-- | Folds 'varBindings' over a list of expressions with a given set of initial bindings
varBindingsList :: (Set Var, Set Binding) -> [Expr] -> (Set Var, Set Binding)
varBindingsList init exprs =
  L.foldl
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
emptyCtxRHS = Lens.set ctxAllocStrategy Decrease emptyCtx

type Config = (Expr, Context, PathCond)

type Result = (Value, Context, PathCond)

type Results = [Result]
