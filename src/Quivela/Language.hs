-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Quivela.Language
    -- * Abbrevs
  ( Addr
  , Config
  , PathCtx
  , Var
    -- * Context
  , Context(..)
  , AllocStrategy(..)
  , ctxAdvCalls
  , ctxAllocStrategy
  , ctxAssumptions
  , ctxFunDecls
  , ctxObjs
  , ctxScope
  , ctxThis
  , ctxTypeDecls
  , emptyCtx
  , emptyCtxRHS
  , findMethod
  , nextAddr
    -- * Diff
  , Diff(..)
    -- * Expr
  , Expr(..)
  , MethodKind(..)
    -- ECall
  , callArgs
  , callName
  , callObj
    -- ESetCompr
  , comprPred
  , comprValue
  , comprVar
    -- EFunDecl
  , efunDeclArgs
  , efunDeclName
    -- EMethod
  , emethodArgs
  , emethodBody
  , emethodKind
  , emethodName
    -- EASsign
  , lhs
  , rhs
    -- ENew
  , newBody
  , newFields
    -- ENewConstr
  , newConstrArgs
  , newConstrName
    -- ETypeDecl
  , typedeclBody
  , typedeclFormals
  , typedeclName
  , typedeclValues
    -- Lists
  , exprsToSeq
  , seqToExprs
    -- Methods
  , nop
  , varBindings
    -- * Field
  , Field(..)
  , fieldInit
  , fieldName
  , fieldType
  , immutable
    -- * FunDecl
  , FunDecl(..)
  , funDeclArgs
  , funDeclName
    -- * Local
  , Local(..)
  , localImmutable
  , localType
  , localValue
    -- * Method
  , Method(..)
  , methodBody
  , methodFormals
  , methodKind
  , methodName
   -- * Object
  , Object(..)
  , adversary
  , emptyObject
  , objAdversary
  , objLocals
  , objMethods
  , objType
  , normalMethods
    -- * Place
  , Place(..)
  , placeConst
  , placeLens
  , placeType
    -- * Proofs
  , Proof
  , ProofPart(..)
  , ProofHint(..)
  , fieldEqual
  , fieldsEqual
   -- * Prop
  , Prop(..)
  , PathCond
  , conjunction
    -- * Results
  , Result
  , Results
  , singleResult
    -- * Type
  , Type(..)
    -- * Value
  , Value(..)
  , SymValue(..)
  , pattern VRef
  , defaultValue
  , isSym
  , symVal
  , valMap
  , valSet
  ) where

import qualified Control.Lens as Lens
import Control.Lens ((<&>), (^.), (^?))
import qualified Control.Monad as Monad
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text.Prettyprint.Doc as P
import Data.Text.Prettyprint.Doc (Doc, Pretty(pretty), (<+>), (<>))
import Quivela.Prelude
import qualified Quivela.Pretty as P
import Quivela.Util (PartialEq(..))

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

instance Pretty Type where
  pretty TInt = pretty "Int"
  pretty (TTuple ts) = P.tupled $ map pretty ts
  pretty (TMap t1 t2) = pretty "Map" <+> pretty t1 <+> pretty t2
  pretty TAny = pretty "Any"
  pretty (TSet t) = pretty "Set" <+> pretty t
  pretty (TNamed s) = pretty s

-- ----------------------------------------------------------------------------
-- Propositions
-- ----------------------------------------------------------------------------
--
-- These are used both to keep track of the path condition
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

instance Pretty Prop where
  pretty (p1 :=: p2) = P.binop "≈" p1 p2
  pretty (Not p) = pretty "¬" <+> pretty p
  pretty (Forall xs p) =
    pretty "∀" <> P.hsep (map (\(v, t) -> pretty v <> P.colon <+> pretty t) xs) <>
    P.dot <+>
    pretty p
  pretty (p1 :=>: p2) = P.binop "⊃" p1 p2
  pretty (p1 :&: p2) = P.binop "∧" p1 p2
  pretty PTrue = pretty "⊤"
  pretty PFalse = pretty "⊥"

conjunction :: [Prop] -> Prop
conjunction [] = PTrue
conjunction [p] = p
conjunction ps = L.foldr1 (:&:) ps

-- | A path condition is a list of propositions that all hold on a given path
-- These could be stored as just one big conjunction instead, but representing
-- them as a list simplifies reasoning about which paths are prefixes of others.
type PathCond = [Prop]

-- ----------------------------------------------------------------------------
-- Expressions
-- ----------------------------------------------------------------------------
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
  -- FIXME: We're losing the information about whether the initial values are const or not
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

prettyArgType :: (String, Type) -> Doc ann
prettyArgType (x, TAny) = pretty x
prettyArgType (x, t) = pretty x <> P.colon <+> pretty t

-- FIXME: Add precedence parentheses
instance Pretty Expr where
  pretty ENop = error "pretty nop"
  pretty (EAssign l r) = pretty l <+> pretty "≔" <+> pretty r
  pretty (EVar x) = pretty x
  pretty (EConst v) = pretty v
  pretty (EProj e v) = pretty e <> P.dot <> pretty v
  pretty (EIdx e1 e2) = pretty e1 <> P.lbracket <> pretty e2 <> P.rbracket
  pretty (ENew fs e) =
    P.nest
      P.step
      (pretty "new" <+> P.tupled (map pretty fs) <+> P.lbrace <> P.line <>
       P.vcat (map pretty (seqToExprs e))) <>
    P.line <>
    P.rbrace
  pretty (ENewConstr n xs) =
    pretty "new" <+> pretty n <> P.tupled (map pretty xs)
  pretty (EMethod f xs e k) =
    P.nest
      P.step
      (pretty k <+> pretty f <> P.tupled (map prettyArgType xs) <+> P.lbrace <>
       P.line <>
       P.vsep (map pretty $ seqToExprs e)) <>
    P.line <>
    P.rbrace
  pretty (ECall (EConst VNil) "&" xs) =
    P.hsep (L.intersperse (pretty "&") (map pretty xs))
  pretty (ECall (EConst VNil) m xs) = pretty m <> P.tupled (map pretty xs)
  pretty (ECall e m xs) =
    pretty e <> P.dot <> pretty m <> P.tupled (map pretty xs)
  pretty (ETuple es) = P.encloseSep P.langle P.rangle P.comma (map pretty es)
  pretty (ETupleProj e1 e2) = pretty e1 <> P.dot <> pretty e2
  pretty (ESeq _ _) = error "pretty seq"
  pretty (EIf e1 e2 e3) =
    P.nest
      P.step
      ((pretty "if" <+> pretty e1) <> P.line <> (pretty "then" <+> pretty e2) <>
       P.line <>
       (pretty "else" <+> pretty e3))
  pretty (EIn x s) = P.binop "∈" x s
  pretty (ESubmap x y) = P.binop "⊆" x y
  pretty (EUnion x y) = P.binop "∪" x y
  pretty (EIntersect x y) = P.binop "∩" x y
  pretty (ETypeDecl name xs vs e) =
    P.nest
      P.step
      (pretty "type" <+> pretty name <>
       P.tupled (L.map (\(x, imm, t) -> P.const imm <> prettyArgType (x, t)) xs) <+>
       P.lbrace <>
       P.line <>
       P.vsep (map (uncurry (P.binop "=")) vs ++ map pretty (seqToExprs e))) <>
    P.line <>
    P.rbrace
  pretty (ESetCompr _ e p) =
    P.lbrace <+> pretty e <+> pretty "|" <+> pretty p <+> P.rbrace
  pretty (EMapCompr x e p) =
    P.lbracket <+> pretty x <+> pretty "↦" <+> pretty e <+> pretty "|" <+>
    pretty p <+>
    P.rbracket
  pretty (EAssume e1 e2) =
    pretty "assume" <+> pretty e1 <+> pretty "≈" <+> pretty e2
  pretty (EFunDecl f xs) = pretty f <> P.tupled (map pretty xs)

nop :: Expr
nop = ENop

seqToExprs :: Expr -> [Expr]
seqToExprs ENop = []
seqToExprs (ESeq e1 e2) = seqToExprs e1 ++ seqToExprs e2
seqToExprs x = [x]

exprsToSeq :: [Expr] -> Expr
exprsToSeq = L.foldr ESeq ENop

-- | Data type for field initializers
data Field = Field
  { _fieldName :: String
  , _fieldInit :: Expr
    -- ^ Expression to initialize the field with
  , _fieldType :: Type
  , _immutable :: Bool
    -- ^ Is the field constant?
  } deriving (Eq, Show, Ord, Data, Generic)

instance Serialize Field

instance Pretty Field where
  pretty (Field x e t imm) =
    P.const imm <> prettyArgType (x, t) <+> P.equals <+> pretty e

data MethodKind
  = NormalMethod
  | LocalMethod
  | Invariant
  deriving (Eq, Show, Ord, Data, Generic)

instance Pretty MethodKind where
  pretty NormalMethod = pretty "method"
  pretty LocalMethod = pretty "local"
  pretty Invariant = pretty "invariant"

instance Serialize MethodKind

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

instance Pretty SymValue where
  pretty (SymVar x t) = pretty x <> P.colon <+> pretty t
  pretty (Insert k v m) =
    P.lbracket <> pretty k <+> pretty "↦" <+> pretty v <> P.rbracket <> pretty m
  pretty (Proj v i) = pretty v <> P.dot <> pretty i
  pretty (Lookup m x) = pretty m <> P.dot <> pretty x
  pretty (AdversaryCall xs) =
    pretty "adversary" <> P.tupled [P.list $ L.map (P.list . map pretty) xs]
  pretty (Add x y) = P.binop "+" x y
  pretty (Sub x y) = P.binop "-" x y
  pretty (Mul x y) = P.binop "*" x y
  pretty (Div x y) = P.binop "/" x y
  pretty (Lt x y) = P.binop "<" x y
  pretty (Le x y) = P.binop "≤" x y
  pretty (SetCompr e x p) =
    P.lbrace <> pretty e <+> pretty "|" <+> pretty x <+> pretty "∈" <+> pretty p <>
    P.rbrace
  pretty (ITE p v1 v2) =
    pretty "if" <+> pretty p <+> pretty "then" <+> pretty v1 <+> pretty "else" <+>
    pretty v2
  pretty (MapCompr x e1 e2) =
    P.lbracket <> pretty x <+> pretty "↦" <+> pretty e1 <+> pretty "|" <+>
    pretty e2 <>
    P.rbracket
  pretty (In x s) = P.binop "∈" x s
  pretty (Union x s) = P.binop "∪" x s
  pretty (MapUnion m1 m2) = P.binop "∪" m1 m2
  pretty (Intersect s1 s2) = P.binop "∩" s1 s2
  pretty (Submap m1 m2) = P.binop "⊆" m1 m2
  pretty (SymRef x) = pretty x
  pretty (Ref x) = pretty "ref" <+> pretty x
  pretty (Deref e m) = pretty e <> P.dot <> pretty m
  pretty (Z v) = pretty "Z" <> P.tupled [pretty v]
  pretty (Call f vs) = pretty f <> P.tupled (map pretty vs)

-- Define how to insert into a symbolic value via a lens:
type instance Lens.Index SymValue = Value

type instance Lens.IxValue SymValue = Value

instance Lens.Ixed SymValue where
  ix k f m = f (Sym $ Lookup k (Sym m)) <&> \v' -> Insert k v' (Sym m)

-- | Quivela values
data Value
  = VInt Integer
  | VMap { _valMap :: Map Value Value } -- TODO: Can any keys or elems be Syms?
  | VTuple [Value]
  | VNil
  | VSet { _valSet :: Set Value } -- TODO: Can any elems be Syms?
  | Sym { _symVal :: SymValue }
  deriving (Eq, Show, Ord, Data, Generic)

instance Serialize Value

instance Pretty Value where
  pretty (VInt n) = pretty n
  pretty (VMap m) = P.mapP m
  pretty (VTuple vs) = P.tupled $ map pretty vs
  pretty VNil = pretty "nil"
  pretty (VSet s) = P.setP s
  pretty (Sym v) = pretty v

-- | Value to use to initialize new variables:
defaultValue :: Value
defaultValue = VInt 0

isSym :: Value -> Bool
isSym (Sym _) = True
isSym _ = False

-- Since we pattern-match repeatedly on references in various places, we define
-- a pattern synonym that handles the fact that references are actually symbolic
pattern VRef :: Addr -> Value

pattern VRef a = Sym (Ref a)

-- | The value of a field of an object in the heap
data Local = Local
  { _localValue :: Value
  , _localType :: Type
  , _localImmutable :: Bool
  } deriving (Eq, Show, Ord, Data)

Lens.makeLenses ''Local

data Method = Method
  { _methodName :: String
  , _methodFormals :: [(String, Type)]
  , _methodBody :: Expr
  , _methodKind :: MethodKind
  } deriving (Eq, Show, Ord, Data)

instance Pretty Method where
  pretty (Method n fs b k) =
    P.nest
      P.step
      (pretty k <+> pretty n <> P.tupled (L.map prettyArgType fs) <+> P.lbrace <>
       P.line <>
       P.vcat (map pretty $ seqToExprs b)) <>
    P.line <>
    P.rbrace

Lens.makeLenses ''Method

data Object = Object
  { _objLocals :: Map Var Local
  , _objMethods :: Map Var Method
  , _objType :: Type
    -- ^ Type of the object if it was constructed with a named type constructor
  , _objAdversary :: Bool -- ^ Is the object an adversary?
  } deriving (Eq, Show, Ord, Data)

instance Pretty Object where
  pretty (Object l m typ a) =
    P.object
      (L.concat
         [ [ pretty "type" <+> P.equals <+> pretty typ
           , pretty "adversary" <+> P.equals <+> pretty a
           ]
         , map
             (\(x, (Local v t imm)) ->
                P.const imm <> prettyArgType(x, t) <+> P.equals <+>
                pretty v)
             (M.toList l)
         , map pretty (M.elems m)
         ])

emptyObject :: Object
emptyObject = Object M.empty M.empty TAny False

adversary :: Object
adversary = emptyObject {_objAdversary = True}

normalMethods :: Object -> [Method]
normalMethods o =
  L.filter (\m -> _methodKind m == NormalMethod) (M.elems (_objMethods o))

-- | To make our lives easier reasoning about equivalences that require
-- new to be commutative, we would like the address identifiers used on the left-hand
-- side and the right-hand side to be disjoint. We implement this by using negative
-- numbers for addresses on the right-hand side and positive numbers otherwise. This
-- datatype encodes which allocation scheme to use.
data AllocStrategy
  = Increase
  | Decrease
  deriving (Eq, Show, Ord, Data)

data FunDecl = FunDecl
  { _funDeclName :: String
  , _funDeclArgs :: [Var]
  } deriving (Eq, Show, Ord, Data)

instance Pretty FunDecl where
  pretty (FunDecl f xs) = pretty f <> P.tupled (L.map pretty xs)

Lens.makeLenses ''FunDecl

data Binding = Binding
  { _bindingName :: Var
  , _bindingConst :: Bool
  } deriving (Eq, Ord, Show)

data Diff
  = NewField Field
  | DeleteField Var
  | OverrideMethod Expr -- assumes expr is an EMethod
  | DeleteMethod Var
  deriving (Show, Eq, Ord)

-- ----------------------------------------------------------------------------
-- Context
-- ----------------------------------------------------------------------------
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

Lens.makeLenses ''Context

instance Pretty Context where
  pretty (Context { _ctxObjs
                  , _ctxThis
                  , _ctxScope
                  , _ctxAdvCalls
                  , _ctxTypeDecls
                  , _ctxAllocStrategy
                  , _ctxAssumptions
                  , _ctxFunDecls
                  }) =
    P.record
      [ ("adversary-calls", P.list $ map (P.list . map pretty) _ctxAdvCalls)
      , ("alloc-strategy", pretty $ show _ctxAllocStrategy)
      , ( "assums"
        , (P.align . P.vcat) $
          L.map
            (\(l, r) -> pretty l <+> pretty "≈" <+> pretty r)
            _ctxAssumptions)
      , ("fundecls", (P.align . P.vcat) $ L.map pretty (M.elems _ctxFunDecls))
      , ("objects", P.mapP _ctxObjs)
      , ( "scope"
        , P.map $
          L.map
            (\(x, (v, t)) -> (pretty x, pretty v <> P.colon <+> pretty t))
            (M.toList _ctxScope))
      , ("this", pretty _ctxThis)
      , ("typedecls", P.mapP _ctxTypeDecls)
      ]

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
emptyCtxRHS = emptyCtx {_ctxAllocStrategy = Decrease}

-- | Return an unused address in the current context
nextAddr :: Context -> Addr
nextAddr ctx =
  case ctx ^. ctxAllocStrategy of
    Increase -> L.maximum (M.keys (ctx ^. ctxObjs)) + 1
    Decrease -> L.minimum (M.keys (ctx ^. ctxObjs)) - 1

L.concat <$> Monad.mapM Lens.makeLenses [''Expr, ''Field, ''Object, ''Value]

-- | Try to find a method of the given name in the object at that address
findMethod :: Addr -> Var -> Context -> Maybe Method
findMethod addr name ctx =
  ctx ^? ctxObjs . Lens.ix addr . objMethods . Lens.ix name

-- ----------------------------------------------------------------------------
-- Place
-- ----------------------------------------------------------------------------
data Place = Place
  { _placeLens :: (forall f. Applicative f =>
                               ((Value -> f Value) -> Context -> f Context))
  , _placeConst :: Bool
  , _placeType :: Type
  }

Lens.makeLenses ''Place

-- ----------------------------------------------------------------------------
-- Proof hints
-- ----------------------------------------------------------------------------
-- | Proof hints include relational invariants, use of assumptions
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

-- | Convenience function for expression that both sides agree on looking
-- up a series of fields. @[a, b, c]@ represents looking up field @a.b.c@.
fieldsEqual :: [Var] -> [Var] -> ProofHint
fieldsEqual fieldsL fieldsR = EqualInv (getField fieldsL) (getField fieldsR)
  where
    getField :: [Var] -> Addr -> Context -> Value
    getField [] _ _ = error "Empty list of fields"
    getField [x] addr ctx
      | Just v <-
         ctx ^? ctxObjs . Lens.ix addr . objLocals . Lens.ix x . localValue = v
      | otherwise = error $ "getField: No such field: " ++ x
    getField (x:xs) addr ctx
      | Just (VRef addr') <-
         ctx ^? ctxObjs . Lens.ix addr . objLocals . Lens.ix x . localValue =
        getField xs addr' ctx
      | otherwise = error $ "Non-reference in field lookup"

-- | Like 'fieldsEqual' but looking up the same fields on both sides.
fieldEqual :: [Var] -> ProofHint
fieldEqual fields = fieldsEqual fields fields

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
         S.map _bindingName fieldsBound)
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
  ( free1 `S.union` (free2 `S.difference` S.map _bindingName bound1)
  , bound1 `S.union` bound2)

-- | Folds 'varBindings' over a list of expressions with a given set of initial bindings
varBindingsList :: (Set Var, Set Binding) -> [Expr] -> (Set Var, Set Binding)
varBindingsList init exprs =
  L.foldl
    (\(freeAcc, boundAcc) expr ->
       let (freeExpr, boundExpr) = varBindings expr
        in ( (freeAcc `S.union` freeExpr) `S.difference`
             S.map _bindingName boundAcc
           , boundAcc `S.union` boundExpr))
    init
    exprs

type PathCtx a = (a, Context, PathCond)

type Config = PathCtx Expr

type Result = PathCtx Value

type Results = [Result]

-- | Throws an error if there is more than one result in the list. Used for
-- evaluating programs that are not supposed to have more than one result.
singleResult :: Results -> Result
singleResult [res@(_, _, _)] = res
singleResult ress = error $ "Multiple results: " ++ show ress
