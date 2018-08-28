{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Quivela.Language where

import Control.Applicative ((<$>))
import Control.Arrow (second)
import Control.Monad
import Control.Lens hiding (Context(..))
import Control.Lens.At
import Control.Monad.RWS.Strict
import Control.Monad.List
import Data.List
import Data.Data
import Data.Maybe
import Data.Serialize (get, put, Serialize)
import Data.Typeable
import qualified Data.Map as M
import qualified Data.Set as S
import GHC.Generics
import System.Process
import System.IO

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
data Type = TInt | TTuple [Type] | TMap Type Type | TAny | TNamed String
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | Symbolic values representing unknowns and operations on the
-- Calls to the adversary are also symbolic.
data SymValue = SymVar String Type
  | Insert Value Value Value
  | Proj Value Value
  | Lookup Value Value
  | AdversaryCall [[Value]]
  | Add Value Value
  | Sub Value Value
  | Mul Value Value
  | Div Value Value
  | Le Value Value
  | ITE Prop Value Value
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | Quivela values
data Value = VInt Integer
  | VMap { _valMap :: M.Map Value Value }
  | VTuple [Value]
  | VError
  | VNil
  | VRef Addr
  | Sym { _symVal :: SymValue }
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | Data type for field initializers
data Field = Field { _fieldName :: String
                   , _fieldInit :: Expr -- ^ Expression to initialize the field with
                   , _fieldType :: Type
                   , _immutable :: Bool -- ^ Is the field constant?
                   }
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

data Expr = ENop
          | EAssign { _lhs :: Expr
                    , _rhs :: Expr }
          | EVar Var
          | EConst Value
          | EProj Expr Var
          | EIdx Expr Expr
          | ENew { _newFields :: [Field]
                 , _newBody :: Expr }
          | EMethod { _emethodName :: String
                    , _emethodArgs :: [(String, Type)]
                    , _emethodBody :: Expr
                    , _eisInvariant :: Bool }
          | ECall { _callObj :: Expr
                  , _callName :: String
                  , _callArgs :: [Expr] }
          | ETuple [Expr]
          | ETupleProj Expr Expr
          | ESeq Expr Expr
          | ETypeDecl { _typedeclName :: String
                      , _typedeclFormals :: [(Var, Type)]
                      , _typedeclValues :: [(Var, Value)]
                      , _typedeclBody :: Expr }
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

instance Serialize SymValue
instance Serialize Value
instance Serialize Type
instance Serialize Field
instance Serialize Expr
instance Serialize Prop

-- | The value of a field of an object in the heap
data Local = Local { _localValue :: Value
                   , _localType :: Type
                   , _localImmutable :: Bool }
  deriving (Eq, Read, Show, Ord, Data, Typeable)

data Method = Method { _methodName :: String
                     , _methodFormals :: [(String, Type)]
                     , _methodBody :: Expr
                     , _isInvariant :: Bool
                     }
  deriving (Eq, Read, Show, Ord, Data, Typeable)

data Object = Object { _objLocals :: M.Map Var Local
                     , _objMethods :: M.Map Var Method
                     -- , _objInvariants :: M.Map Var
                     , _objAdversary :: Bool -- ^ Is the object an adversary?
                     }
  deriving (Eq, Read, Show, Ord, Data, Typeable)

-- | Named types are identifiers of more complex types whose semantics are given
-- as Haskell expressions.
type TypeName = String


data Context = Context { _ctxObjs :: M.Map Addr Object
                       , _ctxThis :: Addr
                       , _ctxScope :: Scope -- ^ Keeps track of local variables and arguments in a
                                            -- method call.
                       , _ctxAdvCalls :: [[Value]] -- ^ All adversary calls so far
                       }
  deriving (Eq, Read, Show, Ord, Data, Typeable)


data Place =
  Place { _placeLens :: (forall f. Applicative f => ((Value -> f Value) -> Context -> f Context))
        , _placeConst :: Bool
        , _placeType :: Type }

-- | Propositions. These are used both to keep track of the path condition
-- as well as for the verification conditions we generate later on.
data Prop = Value :=: Value
  | Not Prop
  | Forall [(Var, Type)] Prop
  | Prop :=>: Prop
  | Prop :&: Prop
  | PTrue | PFalse
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | A path condition is a list of propositions that all hold on a given path
-- These could be stored as just one big conjunction instead, but representing
-- them as a list simplifies reasoning about which paths are prefixes of others.
type PathCond = [Prop]

-- | The denotation of a named type specifies what can be assumed about objects of more complex types
-- and what must be shown when assigning to a field of that type.
data TypeDenotation =
  ObjectType { _methodEffects :: M.Map Var ([Value] -> Context -> [(Value, Context, PathCond)])  }
  deriving (Typeable)

data Binding = Binding { _bindingName :: Var
                       , _bindingConst :: Bool }
  deriving (Eq, Ord, Show, Read)

concat <$> mapM makeLenses [ ''Method, ''Object, ''Context, ''Place, ''TypeDenotation
                           , ''Binding, ''Local, ''Field, ''Expr, ''Value ]

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
  | (freeRhs, boundRhs) <- varBindings rhs  =
      (freeRhs, S.insert (Binding { _bindingName = x, _bindingConst = False }) boundRhs)
varBindings (EAssign lhs rhs) = varBindings lhs `bindingSeq` varBindings rhs
varBindings (ESeq e1 e2) = varBindings e1 `bindingSeq` varBindings e2
varBindings (ECall obj name args) =
  let (freeObj, boundObj) = varBindings obj
  in varBindingsList (freeObj, boundObj) args
-- Note that anything assigned to in the body will end in a local scope of the object,
-- so the body cannot introduce new bound variables
varBindings (ENew fields body) =
  let (fieldsFree, fieldsBound) = varBindingsList (S.empty, S.empty) $ map (^. fieldInit) fields
      (bodyFree, bodyBound) = varBindings body
  in ( bodyFree `S.difference` (S.fromList (map (^. fieldName) fields) `S.union`
                                S.map (^. bindingName) fieldsBound)
     , fieldsBound )
varBindings (EProj eobj name) = varBindings eobj
varBindings (EIdx base idx) = varBindings base `bindingSeq` varBindings idx
  -- Variables bound inside a method body are not visible outside:
varBindings (EMethod name args body isInv) =
  let (bodyFree, bodyBound) = varBindings body
  in (bodyFree, S.empty)
varBindings (ETuple elts) = varBindingsList (S.empty, S.empty) elts
varBindings (ETupleProj base idx) = varBindings base `bindingSeq` varBindings idx
varBindings (ETypeDecl name formals values body) =
  varBindings (ENew (map (\(name, typ) -> Field { _fieldName = name
                                                , _fieldType = typ
                                                , _fieldInit = ENop
                                                , _immutable = False }) formals ++
                     map (\(name, value) -> Field { _fieldName = name
                                                  , _fieldType = TAny
                                                  , _fieldInit = EConst value
                                                  , _immutable = False}) values)
                     body)

-- | Combine two pieces of binding information assuming that the second set of bindings
-- is produced by an expression that will be evaluated after the first
bindingSeq :: (S.Set Var, S.Set Binding) -> (S.Set Var, S.Set Binding) -> (S.Set Var, S.Set Binding)
bindingSeq (free1, bound1) (free2, bound2) =
  ( free1 `S.union` (free2 `S.difference` S.map (^. bindingName) bound1)
  , bound1 `S.union` bound2 )

-- | Folds 'varBindings' over a list of expressions with a given set of initial bindings
varBindingsList :: (S.Set Var, S.Set Binding) -> [Expr] -> (S.Set Var, S.Set Binding)
varBindingsList init exprs =
  foldl (\(freeAcc, boundAcc) expr ->
            let (freeExpr, boundExpr) = varBindings expr
            in ( (freeAcc `S.union` freeExpr) `S.difference` S.map (^. bindingName) boundAcc
               , boundAcc `S.union` boundExpr )) init exprs

emptyCtx :: Context
emptyCtx = Context { _ctxObjs = M.fromList [(0, Object { _objLocals = M.empty
                                                       , _objMethods = M.empty
                                                       , _objAdversary = False })]
                   , _ctxThis = 0
                   , _ctxAdvCalls = []
                   , _ctxScope = M.empty }
