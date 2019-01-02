-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Quivela.Verify
  ( Step(Step)
  , proveStep
  ) where

import Control.Applicative ((<*>), (<|>))
import qualified Control.Arrow as Arrow
import qualified Control.Lens as Lens
import Control.Lens ((%=), (.=), (?~), (^.), (^?))
import qualified Control.Monad.RWS.Strict as Monad
import Control.Monad.RWS.Strict (MonadIO, MonadState, MonadWriter, RWST, (=<<))
import qualified Data.ByteString as ByteString
import qualified Data.Function as F
import qualified Data.Generics as Generics
import qualified Data.List as L
import Data.List ((\\))
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as Merge
import qualified Data.Maybe as Maybe
import qualified Data.Serialize as Serialize
import qualified Data.Set as S
import qualified Debug.Trace as Trace
import qualified Quivela.Language as Q
import Quivela.Language
  ( Addr
  , Context
  , Expr(..)
  , Local
  , Method
  , MethodKind(..)
  , Object
  , PathCond
  , ProofHint(..)
  , Prop(..)
  , Result
  , Results
  , SymValue(..)
  , Type(..)
  , pattern VRef
  , Value(..)
  , Var
  )
import Quivela.Prelude
import qualified Quivela.SymEval as Q
import Quivela.SymEval (Verify)
import qualified Quivela.Util as Q
import qualified Quivela.VerifyPreludes as Q
import qualified System.IO as IO
import qualified System.IO.Temp as Temp
import qualified System.Timer as Timer

-- ----------------------------------------------------------------------------
-- Util
-- ----------------------------------------------------------------------------
maybeInsert :: (Ord k, Eq v) => k -> v -> Map k v -> Maybe (Map k v)
maybeInsert k v m =
  case M.lookup k m of
    Just v' ->
      if v == v'
        then Just m
        else Nothing
    Nothing -> Just (M.insert k v m)

tryInsert :: (Show k, Show v, Ord k, Eq v) => k -> v -> Map k v -> Map k v
tryInsert k v m =
  case maybeInsert k v m of
    Just m' -> m'
    Nothing -> error $ "Key " ++ show k ++ " already mapped in " ++ show m

-- ----------------------------------------------------------------------------
-- VC (Verification conditions)
-- ----------------------------------------------------------------------------
data VC = VC
  { _conditionName :: String
    -- ^ Purely for readability purposes when generating code for other solvers
  , _assumptions :: [Prop]
  , _goal :: Prop
  } deriving (Data, Eq, Ord)

instance Show VC where
  show (VC name assms g) =
    L.unlines
      [ "\nName: " ++ name
      , "\nAssumptions: "
      , L.intercalate "\n" (map show assms)
      , "Goal: "
      , show g
      ]

emptyVC :: VC
emptyVC = VC {_conditionName = "noop", _assumptions = [], _goal = PTrue}

Lens.makeLenses ''VC

-- ----------------------------------------------------------------------------
-- Emitter
-- ----------------------------------------------------------------------------
type SolverCmd = String

-- | A monad for emitting code for external tools. In addition to state
-- to keep track of fresh variables, this also includes a writer monad
-- to collect all emitted lines.
newtype Emitter a = Emitter
  { unEmitter :: RWST () [SolverCmd] EmitterState IO a
  } deriving ( Functor
             , Applicative
             , Monad
             , MonadState EmitterState
             , MonadWriter [SolverCmd]
             , MonadIO
             )

runEmitter :: MonadIO m => Context -> Emitter a -> m (a, [SolverCmd])
runEmitter prefix action =
  Monad.liftIO $
  Monad.evalRWST (unEmitter action) () (initialEmitterState prefix)

data EmitterState = EmitterState
  { _nextEmitterVar :: Map String Integer
  , _varTranslations :: Map String String
  , _usedVars :: [(String, String)]
    -- ^ Stores generated fresh variables and their type in the solver
  , _emitterPrefixCtx :: Context
    -- ^ We make the context of the "prefix"
    -- program of a proof available to emitters so
    -- they can generate output for uninterpreted
    -- functions, etc.
  } deriving (Eq, Data, Ord, Show)

initialEmitterState :: Context -> EmitterState
initialEmitterState prefixCtx =
  EmitterState
    { _nextEmitterVar = M.empty
    , _usedVars = []
    , _varTranslations = M.empty
    , _emitterPrefixCtx = prefixCtx
    }

Lens.makeLenses ''EmitterState

-- TODO: merge with previous implementation
freshEmitterVar :: String -> String -> Emitter String
freshEmitterVar prefix' typ = do
  let prefix = L.filter (`L.notElem` "?") prefix'
  last <- Lens.use (nextEmitterVar . Lens.at prefix)
  case last of
    Just n -> do
      nextEmitterVar . Lens.ix prefix %= (+ 1)
      let varName = prefix ++ show n
      usedVars %= ((varName, typ) :)
      return varName
    Nothing -> do
      Monad.modify (nextEmitterVar . Lens.at prefix ?~ 0)
      freshEmitterVar prefix typ

emit :: SolverCmd -> Emitter ()
emit = Monad.tell . (: [])

-- | Translate a variable name. Caches the result for each variable
-- name so when called with the same variable name again, it will return the same result
-- to make sure that each variable receives a fresh identifier and other occurrences of
-- the same variable receive the same name.
translateVar :: String -> String -> Emitter String
translateVar v typ = do
  translated <- Monad.gets (\s -> s ^? (varTranslations . Lens.ix v))
  case translated of
    Just tv -> return tv
    Nothing -> do
      tv <- freshEmitterVar v typ -- TODO: think if we really need something fresh here, since we're only using this with fresh variables generated by the VCG
      Monad.modify (\s -> varTranslations . Lens.at v ?~ tv $ s)
      return tv

z3Call :: String -> [String] -> String
z3Call fun args = "(" ++ fun ++ " " ++ L.intercalate " " args ++ ")"

-- | Type class for values that can be converted into Z3 terms/formulas
-- TODO: Replace String with Text.PrettyPrint.Doc
class ToZ3 a where
  toZ3 :: a -> Emitter String
  toZ3 = fmap (const "") . toZ3_
  z3CallM :: String -> [a] -> Emitter String
  z3CallM fun args = z3Call fun <$> Monad.mapM toZ3 args
  toZ3_ :: a -> Emitter ()
  toZ3_ = fmap (const ()) . toZ3

instance ToZ3 Integer where
  toZ3 = return . show

instance ToZ3 Type where
  toZ3 TAny = return "Value"
  toZ3 TInt = return "Int"
  toZ3 _ = return "Value"

instance ToZ3 Prop where
  toZ3 PTrue = return "true"
  toZ3 PFalse = return "false"
  toZ3 (Not p) = z3CallM "not" [p]
  toZ3 (x :=: y) = z3CallM "=" [x, y]
  toZ3 (x :=>: y) = z3CallM "=>" [x, y]
  toZ3 (x :&: y) = z3CallM "and" [x, y]
  toZ3 (Forall [] p) = toZ3 p
  toZ3 (Forall formals p) = do
    argNames <-
      Monad.mapM
        (\(x, t) -> (,) <$> (translateVar x =<< toZ3 t) <*> pure t)
        formals
    (fmap L.concat . Monad.sequence)
      [ pure "(forall ("
      , L.intercalate " " <$>
        Monad.mapM
          (\(n, t) -> do
             typ <- toZ3 t
             return $ "(" ++ n ++ " " ++ typ ++ ")")
          argNames
      , pure ") "
      , toZ3 p
      , pure ")"
      ]

-- To make life easier for Z3, we keep all the data types involved monomorphic,
-- so we have separate types in Z3 for values, lists of values, and lists of lists of values:
instance ToZ3 [Value] where
  toZ3 [] = return "nil"
  toZ3 (v:vs) = z3Call "cons" <$> Monad.sequence [toZ3 v, toZ3 vs]

instance ToZ3 [[Value]] where
  toZ3 [] = return "nils"
  toZ3 (vs:vss) = z3Call "conss" <$> Monad.sequence [toZ3 vs, toZ3 vss]

instance ToZ3 Value where
  toZ3 (VInt i) = return $ z3Call "VInt" [show i]
  toZ3 (VTuple vs) = z3Call "VTuple" <$> Monad.sequence [toZ3 vs]
  toZ3 (VMap mp) = do
    elts <-
      Monad.foldM
        (\m (k, v) -> z3Call "store" <$> Monad.sequence [pure m, toZ3 k, toZ3 v])
        "empty-map"
        (M.toList mp)
    return $ z3Call "VMap" [elts]
  toZ3 VNil = return "VNil"
  toZ3 (Sym (Ref addr)) =
    return $ z3Call "vref" [show addr] -- vref is an uninterpreted function instead of a constructor
  toZ3 (Sym sv) = toZ3 sv
  toZ3 (VSet vs) =
    z3Call "VSet" <$>
    Monad.sequence
      [ Monad.foldM
          (\s v ->
             z3Call "store" <$> Monad.sequence [pure s, toZ3 v, pure "true"])
          "empty-set"
          (S.toList vs)
      ]

instance ToZ3 SymValue where
  toZ3 (SymVar x t) =
    case t of
      TInt -> z3Call "VInt" <$> Monad.sequence [translateVar x "Int"]
      _ -> translateVar x "Value"
  toZ3 (Insert k v m) = z3CallM "insert" [k, v, m]
  toZ3 (Lookup k m) = z3CallM "lookup" [k, m]
  toZ3 (AdversaryCall vss) = z3Call "adversary" <$> Monad.sequence [toZ3 vss]
  toZ3 (Proj tup idx) = z3CallM "proj" [tup, idx]
  toZ3 (Add v1 v2) = z3CallM "add" [v1, v2]
  toZ3 (Sub v1 v2) = z3CallM "sub" [v1, v2]
  toZ3 (Mul v1 v2) = z3CallM "mul" [v1, v2]
  toZ3 (Div v1 v2) = z3CallM "divi" [v1, v2]
  toZ3 (Le v1 v2) = z3CallM "le" [v1, v2]
  toZ3 (Lt v1 v2) = z3CallM "lt" [v1, v2]
  toZ3 (ITE tst thn els) =
    z3Call "ite" <$> Monad.sequence [toZ3 tst, toZ3 thn, toZ3 els]
  toZ3 (SymRef name) =
    z3Call "vref" <$> Monad.sequence [translateVar name "Int"]
  toZ3 (Deref obj name) =
    z3Call "deref" <$> Monad.sequence [toZ3 obj, pure ("\"" ++ name ++ "\"")]
  toZ3 (Ref a) = z3Call "vref" <$> Monad.sequence [toZ3 a]
  toZ3 (Z v) = z3CallM "Z" [v]
  toZ3 (Call fun args) = z3CallM fun args
  toZ3 (SetCompr (Sym (SymVar xV TAny)) x pred)
    -- TODO: emit assumptions and newly introduced variables differently so we can handle
    -- them cleanly when occurring in a negative position
   = do
    setVar <- freshEmitterVar ("setcompr_" ++ x) "(Array Value Bool)"
    xCode <- translateVar xV "Value"
    predCode <- toZ3 pred
    emit . L.unlines $
      [ "(assert (forall ((" ++ xCode ++ " Value))"
      , "  (= (select " ++ setVar ++ " " ++ xCode ++ ")"
      , "      " ++ predCode ++ ")))"
      ]
    return $ z3Call "VSet" [setVar]
  toZ3 (SetCompr _ _ _) = freshEmitterVar "setCompr" "Value"
  -- set comprehensions with map not supported in z3 backend
  toZ3 (MapCompr x val pred) = do
    mapVar <- freshEmitterVar ("mapcompr_" ++ x) "(Array Value Value)"
    emit $ "(declare-const " ++ mapVar ++ " (Array Value Value))"
    xT <- translateVar x "Value"
    predT <- toZ3 pred
    valT <- toZ3 val
    -- if the predicate is satisfied, we map x to f(x)
    emit . L.unlines $
      [ "(assert (forall ((" ++ xT ++ " Value))"
      , "  (=> " ++ predT
      , "      (= (select " ++ mapVar ++ " " ++ xT ++ ")"
      , "         " ++ valT ++ "))))"
      ]
    -- otherwise, x is not in the map:
    emit . L.unlines $
      [ "(assert (forall ((" ++ xT ++ " Value))"
      , "  (=> (not " ++ predT ++ ")"
      , "      (= (select " ++ mapVar ++ " " ++ xT ++ ")"
      , "         (VInt 0)))))"
      ]
    return $ z3Call "VMap" [mapVar]
  toZ3 (Union s1 s2) = z3CallM "vunion" [s1, s2]
  toZ3 (Intersect s1 s2) = z3CallM "vintersect" [s1, s2]
  toZ3 (MapUnion m1 m2) = z3CallM "munion" [m1, m2]
  toZ3 (In elt s) = z3CallM "vmember" [elt, s]
  toZ3 (Submap v1 v2) = z3CallM "is-submap" [v1, v2]

instance ToZ3 VC where
  toZ3_ vc
    -- Emit declarations for uninterpreted functions:
   = do
    decls <- Lens.use (emitterPrefixCtx . Q.ctxFunDecls)
    _ <-
      Monad.forM decls $ \decl -> do
        emit
          (z3Call
             "declare-fun"
             [ decl ^. Q.funDeclName
             , "(" ++
               L.intercalate
                 " "
                 (L.replicate (L.length (decl ^. Q.funDeclArgs)) "Value") ++
               ")"
             , "Value"
             ])
        -- FIXME: For debugging the envelope encryption proof, we emit an assumption that skenc never fails to encrypt.
        -- To do this properly, we'd allow specifying such assumptions in the surface syntax
        Monad.when (decl ^. Q.funDeclName == "skenc") $
          emit
            (z3Call
               "assert"
               [ z3Call
                   "forall"
                   [ "(" ++
                     L.intercalate
                       " "
                       (map
                          (\arg -> "(" ++ arg ++ " Value)")
                          (decl ^. Q.funDeclArgs)) ++
                     ")"
                   , z3Call
                       "not"
                       [ z3Call
                           "="
                           [ z3Call
                               (decl ^. Q.funDeclName)
                               (decl ^. Q.funDeclArgs)
                           , "(VInt 0)"
                           ]
                       ]
                   ]
               ])
    emit $ ";; " ++ (vc ^. conditionName)
    -- FIXME: this is a hacky way to make sure we output the variable
    -- declarations before the places where we need them.
    -- Really we should be doing this in a more structured way.
    (translatedAssms, assmOutput) <-
      Q.intercept $ Monad.mapM toZ3 (vc ^. assumptions)
    (goalProp, goalOutput) <- Q.intercept $ toZ3 (vc ^. goal)
    vars <- Lens.use usedVars
    _ <-
      Monad.forM vars $ \(var, typ) -> emit $ z3Call "declare-const" [var, typ]
    Monad.mapM_ emit (assmOutput ++ goalOutput)
    Monad.mapM_ (\asm -> emit (z3Call "assert" [asm])) translatedAssms
    emit $ z3Call "assert" [z3Call "not" [goalProp]]

-- ----------------------------------------------------------------------------
-- Havocing
-- ----------------------------------------------------------------------------
-- | Havoc a local variable if it's not an immutable variable
havocLocal :: Var -> Local -> Verify Local
havocLocal name l
  | not (Lens.view Q.localImmutable l) = do
    fv <- Q.freshVar name
    return $ Lens.set Q.localValue (Sym (SymVar fv (l ^. Q.localType))) l
  | otherwise = return l

-- | Havoc all non-immutable locals of an object
havocObj :: Object -> Verify Object
havocObj obj
  | obj ^. Q.objAdversary = return obj
    -- ^ this is a hack, since we currently don't support const annotations on global variables
  | otherwise = do
    newLocals <-
      Monad.mapM
        (\(name, loc) -> (name, ) <$> havocLocal name loc)
        (M.toList (obj ^. Q.objLocals))
    return (Lens.set Q.objLocals (M.fromList newLocals) obj)

-- | Havoc all objects in a context
havocContext :: Context -> Verify Context
havocContext = Generics.everywhereM (Generics.mkM havocObj)

-- | Check if the goal is trivial (equalities like x = x, a goal occurring as an assumption,
-- and having both P and (not P) as an assumption)
triviallyTrue :: VC -> Verify Bool
triviallyTrue vc
  | v1 :=: v1' <- vc ^. goal =
    return $ (v1 == v1') || assumptionsContradictory (vc ^. assumptions)
  | (vc ^. goal) `L.elem` (vc ^. assumptions) = return True
  | otherwise = return False
  where
    assumptionsContradictory assms =
      L.any
        (\asm ->
           case asm of
             Not p -> L.any (\asm' -> asm' == p) assms -- FIXME: this probably shouldn't be quadratic
             _ -> False)
        assms

-- | Compute all relational proof obligations generated by an invariant
invToVC ::
     [Prop] -> Addr -> Result -> Addr -> Result -> ProofHint -> Verify [VC]
invToVC assms addrL (_, ctxL, pathCondL) addrR (_, ctxR, pathCondR) inv =
  case inv of
    EqualInv f g ->
      return $
      [ emptyVC
          { _assumptions = L.nub $ pathCondL ++ pathCondR ++ assms -- FIXME: Maintain `nub` invariant in data structure, not at each record update.
          , _conditionName = "equalInvPreserved"
          , _goal = f addrL ctxL :=: g addrR ctxR
          }
      ]
    _ -> return []

-- | Convert an invariant into assumptions. Note that for universal
-- invariants, this produces several assumptions.
invToAsm :: Result -> Result -> ProofHint -> Verify [Prop]
invToAsm (VRef addrL, ctxL, _) (VRef addrR, ctxR, _) inv =
  case inv of
    EqualInv f g -> return [f addrL ctxL :=: g addrR ctxR]
    _ -> return []
invToAsm _ _ _ = error "invToAsm called with non-address arguments"

-- | Return all invariant methods in given context
collectInvariants :: Addr -> Context -> [Method]
collectInvariants addr ctx =
  L.filter (\mtd -> mtd ^. Q.methodKind == Invariant) . M.elems $ ctx ^.
  (Q.ctxObjs . Lens.ix addr . Q.objMethods)

-- | Return all non-relational proof obligations generated by invariants
invToVCnonRelational :: [Prop] -> Addr -> Result -> Verify [VC]
invToVCnonRelational assms addr (_, ctx, pathCond) = do
  let univInvs = collectInvariants addr ctx
  fmap L.concat . Monad.forM univInvs $ \univInv -> do
    let formals = univInv ^. Q.methodFormals
    (args, ctx', pathCond') <- Q.symArgs ctx formals
    let scope =
          M.fromList (L.zip (map fst formals) (L.zip args (map snd formals)))
    paths <-
      Q.symEval
        ( univInv ^. Q.methodBody
        , Lens.set Q.ctxThis addr (Lens.set Q.ctxScope scope ctx')
        , pathCond' ++ pathCond)
    Q.foreachM (return paths) $ \(r, _, pathCondI) ->
      return
        [ VC
            { _assumptions = L.nub $ pathCondI ++ assms
            , _conditionName = "univInvPreserved_" ++ (univInv ^. Q.methodName)
            , _goal = Not (r :=: VInt 0)
            }
        ]

onlySimpleTypes :: Data p => p -> Verify ()
onlySimpleTypes foo =
  Monad.when
    (not . L.null . Generics.listify isNamed $ foo)
    (error $ "Symbolic objects as method arguments not yet supported")
  where
    isNamed :: Type -> Bool
    isNamed (TNamed _) = True
    isNamed _ = False

universalInvariantAssms :: Addr -> Context -> PathCond -> Verify [Prop]
universalInvariantAssms addr ctx pathCond =
  fmap L.concat . Monad.forM (collectInvariants addr ctx) $ \invariantMethod -> do
    let formals = invariantMethod ^. Q.methodFormals
    onlySimpleTypes formals
    (args, ctx', pathCond') <- Q.symArgs ctx formals
    let scope =
          M.fromList (L.zip (map fst formals) (L.zip args (map snd formals)))
    let oldRefs = collectRefs ctx'
    let oldSymVars = collectSymVars ctx'
    paths <-
      Q.symEval
        ( invariantMethod ^. Q.methodBody
        , Lens.set Q.ctxThis addr (Lens.set Q.ctxScope scope ctx)
        , pathCond' ++ pathCond)
    let destVar (Sym (SymVar n t)) = (n, t)
        destVar _ = error "Not a var"
    let argNames = map destVar args
    Q.foreachM (return paths) $ \(res, ctxI, pathCondI)
      -- If there were symbolic objects created on demand, we may now have a bunch
      -- of extra symbolic variables that were introduced. Since these are going
      -- to be arbitrary parameters, we have to quantify over them as well here:
      -- TODO: check for duplicate symvars of different types
     -> do
      let newSymVars = collectSymVars (res, ctxI, pathCondI) \\ oldSymVars
      let deref (VRef a) = a
          deref _ = error "Not a ref"
      let newRefs = map deref $ collectRefs (res, ctxI, pathCondI) \\ oldRefs
      refVars <- Monad.mapM (Q.freshVar . ("symref" ++) . show) newRefs
      let replaceRef :: Data p => Addr -> Value -> p -> p
          replaceRef a v = Generics.everywhere (Generics.mkT replace)
            where
              replace (VRef a')
                | a == a' = v
                | otherwise = VRef a'
              replace x = x
          replaceAllRefs :: Data p => p -> p
          replaceAllRefs x =
            L.foldr
              (\(ref, symref) p -> replaceRef ref symref p)
              x
              (L.zip newRefs (map (Sym . SymRef) refVars))
          (vs, assms, conseq) =
            onePointTransform
              (L.nub $ argNames ++ map ((, TInt)) refVars ++ newSymVars)
              pathCondI
              (Not (res :=: VInt 0))
      return $ replaceAllRefs [Forall vs (Q.conjunction assms :=>: conseq)]
  -- | Collect all free symbolic variables occurring in some data
  -- Only forall statements are considered as variable binders.
  where
    collectRefs :: Data p => p -> [Value]
    collectRefs = Generics.listify isRef
      where
        isRef (VRef _) = True
        isRef _ = False
    collectSymVars :: Data p => p -> [(Var, Type)]
    collectSymVars vc =
      L.nubBy ((==) `F.on` fst) . map toTup $
      Generics.everythingWithContext
        []
        (++)
        (Generics.mkQ ((,) []) collect `Generics.extQ` propBind)
        vc
      where
        collect (SymVar x t) bound
          | x `L.notElem` bound = ([SymVar x t], bound)
          | otherwise = ([], bound)
        collect _ bound = ([], bound)
        propBind (Forall formals _) bound = ([], bound ++ map fst formals)
        propBind _ bound = ([], bound)
        toTup (SymVar x t) = (x, t)
        toTup _ = undefined
    -- To make Z3 cope with forall quantifications better, make sure there are no forall-quantified
    -- variables x occurring in one assumption of the form (x = E) by replacing x by E in the
    -- rest of the formula.
    onePointTransform ::
         [(Var, Type)] -> [Prop] -> Prop -> ([(Var, Type)], [Prop], Prop)
    onePointTransform vs assms conseq =
      L.foldr removeVar (vs, assms, conseq) spuriousAssms
      where
        spuriousAssms =
          Maybe.catMaybes $
          map
            (\x ->
               Maybe.listToMaybe . Maybe.catMaybes $
               map
                 (\assm ->
                    case assm of
                      Sym (SymVar y _) :=: e ->
                        if y == x
                          then Just (x, e, assm)
                          else Nothing
                      e :=: Sym (SymVar y _) ->
                        if y == x
                          then Just (x, e, assm)
                          else Nothing
                      _ -> Nothing)
                 assms)
            (map fst vs)
        removeVar (spurVar, spurExpr, origAssm) (vs', assms', conseq') =
          ( L.filter ((/= spurVar) . fst) vs'
          , map (substSymVar spurVar spurExpr) . L.filter (/= origAssm) $ assms'
          , substSymVar spurVar spurExpr conseq')
        -- | Substitute x by v in p
        substSymVar :: Var -> Value -> Prop -> Prop
        substSymVar x v p =
          Generics.everywhereBut
            (Generics.mkQ False binds)
            (Generics.mkT replace)
            p
          where
            binds (Forall vs' _) = L.elem x (map fst vs')
            binds _ = False
            replace (Sym (SymVar y _))
              | x == y = v
            replace e = e

-- ----------------------------------------------------------------------------
-- Address bijections
-- ----------------------------------------------------------------------------
-- | Type synonym for building up bijections between addresses
type AddrBijection = Map Addr Addr

-- | Try to find a mapping for addresses that may make the two values equal.
unifyAddrs :: Value -> Value -> AddrBijection -> AddrBijection
unifyAddrs (VInt _) (VInt _) bij = bij
unifyAddrs (VMap vs1) (VMap vs2) bij =
  L.foldr
    (\(v1, v2) bij' -> unifyAddrs v1 v2 bij')
    bij
    (M.elems $
     Merge.merge
       Merge.dropMissing
       Merge.dropMissing
       (Merge.zipWithMatched (\_ v1 v2 -> (v1, v2)))
       vs1
       vs2)
unifyAddrs (VTuple vs1) (VTuple vs2) bij =
  L.foldr (\(v1, v2) bij' -> unifyAddrs v1 v2 bij') bij (L.zip vs1 vs2)
unifyAddrs (VRef a1) (VRef a2) bij
  | a2 >= 0 = tryInsert a2 a2 bij -- we only want to remap RHS addresses, which are always negative
  | M.lookup a2 bij == Just a1 || M.lookup a2 bij == Nothing =
    M.insert a2 a1 bij
unifyAddrs (Sym s1) (Sym s2) bij
  | Just bij' <- unifyAddrsExactSym s1 s2 bij = bij'
unifyAddrs _ _ bij = bij

unifyAddrsExact :: Value -> Value -> AddrBijection -> Maybe AddrBijection
unifyAddrsExact (VInt i1) (VInt i2) bij
  | i1 == i2 = Just bij
  | otherwise = Nothing
unifyAddrsExact (VMap vs1) (VMap vs2) bij
  | S.fromList (M.keys vs1) == S.fromList (M.keys vs2) =
    Monad.foldM
      (\bij' (v1, v2) -> unifyAddrsExact v1 v2 bij')
      bij
      (M.elems $
       Merge.merge
         Merge.dropMissing
         Merge.dropMissing
         (Merge.zipWithMatched (\_ v1 v2 -> (v1, v2)))
         vs1
         vs2)
unifyAddrsExact (VTuple vs1) (VTuple vs2) bij
  | L.length vs1 == L.length vs2 =
    Monad.foldM
      (\bij' (v1, v2) -> unifyAddrsExact v1 v2 bij')
      bij
      (L.zip vs1 vs2)
  | otherwise = Nothing
unifyAddrsExact VNil VNil bij = Just bij
unifyAddrsExact (Sym sL) (Sym sR) bij = unifyAddrsExactSym sL sR bij
unifyAddrsExact _ _ _ = Nothing

unifyAddrsExactSym ::
     SymValue -> SymValue -> AddrBijection -> Maybe AddrBijection
unifyAddrsExactSym (Ref aL) (Ref aR) bij
  | aR >= 0 =
    if aL == aR
      then Just bij
      else Nothing
  | otherwise = maybeInsert aR aL bij
unifyAddrsExactSym (Lookup kL mL) (Lookup kR mR) bij =
  unifyAddrsExact kL kR bij >>= unifyAddrsExact mL mR
unifyAddrsExactSym (Insert kL vL mL) (Insert kR vR mR) bij =
  unifyAddrsExact kL kR bij >>= unifyAddrsExact vL vR >>= unifyAddrsExact mL mR
unifyAddrsExactSym (Proj tupL idxL) (Proj tupR idxR) bij =
  unifyAddrsExact tupL tupR bij >>= unifyAddrsExact idxL idxR
unifyAddrsExactSym (AdversaryCall valssL) (AdversaryCall valssR) bij
  | L.length valssL == L.length valssR
  , L.and (L.zipWith ((==) `F.on` L.length) valssL valssR) =
    Monad.foldM
      (\bij' (valsL, valsR) ->
         Monad.foldM
           (\bij'' (valL, valR) -> unifyAddrsExact valL valR bij'')
           bij'
           (L.zip valsL valsR))
      bij
      (L.zip valssL valssR)
  | otherwise = Nothing
unifyAddrsExactSym (ITE condL thnL elsL) (ITE condR thnR elsR) bij =
  unifyAddrsExactProp condL condR bij >>= unifyAddrsExact thnL thnR >>=
  unifyAddrsExact elsL elsR
unifyAddrsExactSym (Z vL) (Z vR) bij = unifyAddrsExact vL vR bij
unifyAddrsExactSym (Call funL argsL) (Call funR argsR) bij
  | funL == funR && L.length argsL == L.length argsR =
    Monad.foldM
      (\bij' (argL, argR) -> unifyAddrsExact argL argR bij')
      bij
      (L.zip argsL argsR)
unifyAddrsExactSym sL sR bij
  | sL == sR = Just bij
  | otherwise = Nothing

unifyAddrsExactProp :: Prop -> Prop -> AddrBijection -> Maybe AddrBijection
unifyAddrsExactProp (Not pL) (Not pR) bij = unifyAddrsExactProp pL pR bij
unifyAddrsExactProp (v1L :=: v2L) (v1R :=: v2R) bij =
  unifyAddrsExact v1L v1R bij >>= unifyAddrsExact v2L v2R
unifyAddrsExactProp PTrue PTrue bij = Just bij
unifyAddrsExactProp PFalse PFalse bij = Just bij
unifyAddrsExactProp (asmL :=>: conseqL) (asmR :=>: conseqR) bij =
  unifyAddrsExactProp asmL asmR bij >>= unifyAddrsExactProp conseqL conseqR
unifyAddrsExactProp (p1L :&: p2L) (p1R :&: p2R) bij =
  unifyAddrsExactProp p1L p1R bij >>= unifyAddrsExactProp p2L p2R
unifyAddrsExactProp pL pR bij
  | pL == pR = Just bij
  | otherwise = Nothing

-- | Try to find a bijection between addresses to be applied to the right-hand
-- side to make both sides possible to be proven equal. This is a best-effort
-- process and may not return a mapping that actually makes them equal, and may
-- not be complete.
findAddressBijection :: AddrBijection -> Result -> Result -> AddrBijection
findAddressBijection inMap (v, _, pathCond) (v', _, pathCond') =
  let baseMap = unifyAddrs v v' inMap
      remainingLHSRefs = allAddrs (v, pathCond) \\ M.elems baseMap
      remainingRHSRefs = allAddrs (v', pathCond') \\ M.keys baseMap
   in extendMap baseMap remainingRHSRefs remainingLHSRefs
  where
    extendMap base [] _ = base
    extendMap base (a:as) (p:ps)
      | a >= 0 = tryInsert a a (extendMap base as (p : ps))
    extendMap base (a:as) (p:ps) = tryInsert a p (extendMap base as ps)
    extendMap base (a:as) [] =
      let base' = (extendMap base as [])
       in tryInsert a (nextFreeAddr base') base'
    nextFreeAddr m
      | L.null (M.elems m) = 100
      | otherwise = L.maximum (M.elems m) + 1
    allAddrs :: Data p => p -> [Addr]
    allAddrs = L.nub . map fromRef . Generics.listify isAddr
      where
        isAddr (Ref _) = True
        isAddr _ = False
        fromRef (Ref a) = a
        fromRef _ = error "fromRef called with non-Ref argument"

-- | Remap all addresses in a piece of data with given bijection.
applyAddressBijection :: Data p => AddrBijection -> p -> p
applyAddressBijection addrMap =
  Generics.everywhere (Generics.mkT replaceAddress)
  where
    replaceAddress :: SymValue -> SymValue
    replaceAddress (Ref addr)
      | addr >= 0 = Ref addr -- new RHS addresses are always negative
      | Just newAddr <- M.lookup addr addrMap = Ref newAddr
      | otherwise = Ref addr -- error $ "No mapping for address: " ++ show addr ++ " in " ++ show addrMap
    replaceAddress v = v

findContradictingBijection :: PathCond -> PathCond -> Maybe AddrBijection
findContradictingBijection [] _ = Nothing
findContradictingBijection (Not propL:pcL') pcR
  -- FIXME: duplication
 =
  case pcR of
    [] -> Nothing
    propR:pcR' ->
      unifyAddrsExactProp propL propR M.empty <|>
      findContradictingBijection (Not propL : pcL') pcR'
findContradictingBijection (propL:pcL') pcR =
  case pcR of
    [] -> Nothing
    Not propR:pcR' ->
      unifyAddrsExactProp propL propR M.empty <|>
      findContradictingBijection (propL : pcL') pcR'
    _:pcR' -> findContradictingBijection (propL : pcL') pcR'

-- | Generate the verification conditions for two sets of results (i.e.
-- configurations returned by evaluating a method call with symbolic arguments
-- in a havoced context). Also takes the old havoced environments as arguments
-- to turn invariants into assumptions.
resultsToVCs ::
     [ProofHint] -> Result -> Results -> Result -> Results -> Verify [VC]
resultsToVCs invs old@(VRef addr1, ctxH, pathCondH) ress1 old'@(VRef addr2, ctxH', pathCondH') ress1' = do
  invAssms <-
    (++) <$> universalInvariantAssms addr1 ctxH pathCondH <*>
    universalInvariantAssms addr2 ctxH' pathCondH'
  assms <- (invAssms ++) . L.concat <$> Monad.mapM (invToAsm old old') invs
  -- Invariant methods aren't relational and hence we don't need to check them for each pair of
  -- of paths:
  lhsInvVCs <- Q.foreachM (return ress1) $ invToVCnonRelational assms addr1
  rhsInvVCs <- Q.foreachM (return ress1') $ invToVCnonRelational assms addr2
  relationalVCs <-
    Q.foreachM (return ress1) $ \res1@(v1, ctx1, pc1) ->
      Q.foreachM (return ress1') $ \res1'@(v1', ctx1', pc1')
        -- if we are able to find a trivial bijection resulting in a
        -- a trivial contradiction in the path conditions, then we are done:
       -> do
        let baseMap =
              case Maybe.catMaybes $
                   map
                     (\hint ->
                        case hint of
                          UseAddressBijection m -> Just m
                          _ -> Nothing)
                     invs of
                [m] ->
                  Trace.trace ("Using user-supplied address map: " ++ show m) $
                  m
                [] -> M.empty
                _ -> error "More than one address bijection hint"
        let addrMap =
              Maybe.fromMaybe
                (findAddressBijection baseMap res1 res1')
                (findContradictingBijection pc1 pc1')
            applyBij :: Data p => p -> p
            applyBij =
              if NoAddressBijection `Q.elemPartial` invs
                then id
                else applyAddressBijection addrMap
        -- Note that it's fine to only use the address bijection for relational proof
        -- obligations, since non-relational VCs should can not depend on concrete addresses
        -- that the allocator chose.
        let vcRes =
              VC
                { _assumptions = applyBij $ L.nub $ assms ++ pc1 ++ pc1'
                , _conditionName = "resultsEq"
                , _goal = id (v1 :=: applyBij v1')
                }
        invVCs <-
          if ctx1 == ctxH && ctx1' == ctxH'
            then return []
            else L.concat <$>
                 Monad.mapM
                   (fmap applyBij . invToVC assms addr1 res1 addr2 res1')
                   invs
        -- Require that adversary was called with same values:
        let vcAdv =
              VC
                { _assumptions = applyBij $ L.nub $ assms ++ pc1 ++ pc1'
                , _conditionName = "advCallsEq"
                , _goal =
                    Sym (AdversaryCall (ctx1 ^. Q.ctxAdvCalls)) :=:
                    applyBij (Sym (AdversaryCall (ctx1' ^. Q.ctxAdvCalls)))
                }
        return $ vcRes : vcAdv : invVCs
  return $ relationalVCs ++ lhsInvVCs ++ rhsInvVCs
resultsToVCs _ (v1, _, _) _ (v1', _, _) _ =
  error $ "resultsToVCs called with non-address values" ++ show (v1, v1')

-- | Collect non-trivial verification conditions for a given method, invariants and arguments
methodEquivalenceVCs ::
     Method -> [ProofHint] -> [Value] -> Result -> Result -> Verify [VC]
methodEquivalenceVCs mtd invs args (VRef a1, ctx1, pathCond1) (VRef a1', ctx1', pathCond1') = do
  ctxH1 <- havocContext ctx1
  ctxH1' <- havocContext ctx1'
  results <-
    Q.symEval
      ( ECall (EConst (VRef a1)) (mtd ^. Q.methodName) (map EConst args)
      , ctxH1
      , pathCond1)
  results' <-
    Q.symEval
      ( ECall (EConst (VRef a1')) (mtd ^. Q.methodName) (map EConst args)
      , if NoAddressBijection `Q.elemPartial` invs
          then ctxH1'
          else Lens.set Q.ctxAllocStrategy Q.Decrease ctxH1'
      , pathCond1')
  vcs <-
    resultsToVCs
      invs
      (VRef a1, ctxH1, pathCond1)
      results
      (VRef a1', ctxH1', pathCond1')
      results'
  Monad.filterM
    (\vc -> do
       trivial <- triviallyTrue vc
       if trivial
         then do
           return False
         else return True)
    vcs
methodEquivalenceVCs _ _ _ (v1, _, _) (v1', _, _) =
  error $ "methodEquivalenceVCs called with non-reference values: " ++
  show (v1, v1')

-- | Verify conditions with external solvers and return unverified conditions
checkVCs :: [VC] -> Verify [VC]
checkVCs [] = return []
checkVCs vcs = do
  Q.debug $ show (L.length vcs) ++ " verification conditions"
  (t, vcs') <- Timer.time $ Monad.filterM (fmap not . checkWithZ3) vcs
  Monad.unless (L.null vcs') $ do
    Q.debug "Remaining VCs in Z3 files: "
    Monad.mapM_ writeToZ3File vcs'
  Q.debug $ show (L.length vcs') ++ " VCs left after checking with Z3 (" ++
    Timer.formatSeconds t ++
    ")"
  return vcs'
  where
    writeToZ3File :: VC -> Verify ()
    writeToZ3File vc = do
      tmp <- Monad.liftIO Temp.getCanonicalTemporaryDirectory
      dir <- Monad.liftIO $ Temp.createTempDirectory tmp "vcs"
      prelude <- Monad.liftIO Q.z3Prelude
      pctx <- Lens.use Q.verifyPrefixCtx
      ((), vcLines') <- runEmitter pctx (toZ3_ vc)
      -- FIXME: This nub is required, but I have no idea why.  Remove it when you figure it out.
      let vcLines = L.nub vcLines'
      let lines = prelude : vcLines ++ ["(check-sat)"]
      tempFile <-
        Monad.liftIO $ Temp.writeTempFile dir "z3-vc.smt2" (L.unlines lines)
      Q.debug ("Writing vc to file: " ++ tempFile)
    checkWithZ3 :: VC -> Verify Bool
    checkWithZ3 vc = do
      write <- Lens.view Q.writeAllVCsToFile
      Monad.when write (writeToZ3File vc)
      pctx <- Lens.use Q.verifyPrefixCtx
      ((), vcLines') <- runEmitter pctx (toZ3_ vc)
      -- FIXME: This nub is required, but I have no idea why.  Remove it when you figure it out.
      let vcLines = L.nub vcLines'
      sendToZ3 "(push)"
      sendToZ3 (L.unlines vcLines)
      sendToZ3 "(check-sat)"
      answer <- readLineFromZ3
      sendToZ3 "(pop)"
      return $ L.isInfixOf "unsat" answer
    sendToZ3 :: String -> Verify ()
    sendToZ3 line = do
      (hin, _, _) <- Lens.use Q.z3Proc
      Monad.liftIO $ IO.hPutStrLn hin line
    readLineFromZ3 :: Verify String
    readLineFromZ3 = do
      (_, hout, _) <- Lens.use Q.z3Proc
      Monad.liftIO $ IO.hGetLine hout

-- ----------------------------------------------------------------------------
-- Step
-- ----------------------------------------------------------------------------

-- | Quivela proofs are a series of equivalent expressions and a list of
-- invariants that are needed to verify this step.
data Step = Step
  { lhs :: Expr
  , hints :: [ProofHint]
  , rhs :: Expr
  }

stepNote :: Step -> String
stepNote Step {hints} =
  L.intercalate ":" $
  Maybe.mapMaybe
    (\case
       Note n -> Just n
       _ -> Nothing)
    hints

checkEqv :: Expr -> Step -> Verify [(Var, [VC])]
checkEqv _ Step {lhs, hints, rhs}
  | Q.elemPartial Admit hints = do
    Q.debug $ "Skipping proof step: " ++ show lhs ++ " ≈ " ++ show rhs
    return []
checkEqv prefix Step {lhs, rhs, hints = [Rewrite from to]} = do
  (_, prefixCtx, _) <- fmap Q.singleResult $ Q.symEval (prefix, Q.emptyCtx, [])
  let assms = prefixCtx ^. Q.ctxAssumptions
  Monad.unless (L.elem (from, to) assms || L.elem (to, from) assms) $
    Monad.fail ("No such assumption: " ++ show from ++ " ≈ " ++ show to)
  let lhs' = rewriteExpr from to lhs
  if lhs' == rhs
    then return []
    else error $ "Invalid rewrite step:" ++ show lhs' ++ " = " ++ show rhs
checkEqv prefix step@Step {lhs, rhs} = do
  cached <- S.member (lhs, rhs) <$> Lens.use Q.alreadyVerified
  step'@Step {hints} <- inferInvariants prefix step
  withCache <- Q.useCache
  let note = stepNote step'
  if withCache && cached && not (Q.elemPartial IgnoreCache hints)
    then do
      Q.debug "Skipping cached verification step"
      return []
    else do
      (_, prefixCtx, pathCond) <-
        Q.singleResult <$> Q.symEval (prefix, Q.emptyCtx, [])
      Q.verifyPrefixCtx .= prefixCtx
      resL@(VRef aL, ctxL, _) <-
        Q.singleResult <$> Q.symEval (lhs, prefixCtx, pathCond)
      resR@(VRef aR, ctxR, _) <-
        Q.singleResult <$> Q.symEval (rhs, prefixCtx, pathCond)
      -- check that invariants hold initially
      invLHS <- invToVCnonRelational [] aL resL
      invRHS <- invToVCnonRelational [] aR resR
      invsRel <- L.concat <$> Monad.mapM (invToVC [] aL resL aR resR) hints
      remainingInvVCs <- checkVCs (invLHS ++ invRHS ++ invsRel)
      let mtds = sharedMethods aL ctxL aR ctxR
      -- check that there are no other methods except invariants:
      let allMethods :: Addr -> Context -> Set String
          allMethods addr ctx =
            S.fromList . map (^. Q.methodName) .
            L.filter ((== NormalMethod) . (^. Q.methodKind)) .
            M.elems $
            (ctx ^. Q.ctxObjs . Lens.ix addr . Q.objMethods)
          lhsMethods = allMethods aL ctxL
          rhsMethods = allMethods aR ctxR
      Monad.when (lhsMethods /= rhsMethods) $ do
        let extraMtds =
              (lhsMethods `S.difference` rhsMethods) `S.union`
              (rhsMethods `S.difference` lhsMethods)
        error $ note ++
          "LHS and RHS do not have the same non-invariant methods; extra methods: " ++
          show extraMtds
      (t, remainingVCs) <-
        fmap (Arrow.second ([("_invsInit", remainingInvVCs)] ++)) . Timer.time $
        Monad.forM mtds $ \mtd -> do
          Q.debug $ "Checking method: " ++ mtd ^. Q.methodName
          let formals = mtd ^. Q.methodFormals
          onlySimpleTypes formals
          (args, _, _) <- Q.symArgs ctxL formals
          -- TODO: double-check that we don't need path condition here.
          vcs <- methodEquivalenceVCs mtd hints args resL resR
          verificationResult <- checkVCs vcs
          return (mtd ^. Q.methodName, verificationResult)
      if (not . L.all (L.null . snd) $ remainingVCs)
        then do
          Q.debug "Verification failed"
          Q.debug $ show remainingVCs
        else do
          cacheVerified
          Q.debug $ "Verification succeeded in " ++ Timer.formatSeconds t
      return remainingVCs
  where
    cacheVerified :: Verify ()
    -- | ^ Mark a pair of expressions as successfully verified in the cache
    cacheVerified = do
      f <- Lens.view Q.cacheFile
      case f of
        Nothing -> return ()
        Just f' -> do
          Q.alreadyVerified %= S.insert (lhs, rhs)
          verified <- Lens.use Q.alreadyVerified
          Monad.liftIO $ ByteString.writeFile f' (Serialize.encode verified)
    -- | Find the shared methods between two objects in their respective contexts
    sharedMethods :: Addr -> Context -> Addr -> Context -> [Method]
    sharedMethods addrL ctxL addrR ctxR
      | Just objL <- ctxL ^? Q.ctxObjs . Lens.ix addrL
      , Just objR <- ctxR ^? Q.ctxObjs . Lens.ix addrR =
        let mtdsL = objL ^. Q.objMethods
            mtdsR = objR ^. Q.objMethods
            sharedNames = M.keys mtdsL `L.intersect` M.keys mtdsR
      -- TODO: check that there are no extraneous methods and that they
      -- take the same number (and type) of arguments
         in L.filter ((== NormalMethod) . (^. Q.methodKind)) .
            map (Maybe.fromJust . (`M.lookup` mtdsL)) $
            sharedNames
      | otherwise = error "Invalid addresses passed to sharedMethods"

-- | @'rewriteExpr' from to e@ rewrites all occurrences of @from@ in @e@ by @to@
-- FIXME: This is unsound.  It must take bound variables into account.
-- TODO: Write unit tests for this
rewriteExpr :: Expr -> Expr -> Expr -> Expr
rewriteExpr from to e = Generics.everywhere (Generics.mkT replace) e
  where
    replace :: Expr -> Expr
    replace e'
      | e' == from = to
      | otherwise = e'

-- | When mutable fields with the same name, type, and value are shared between two
--   expressions in a Step, infer they should be equal.
--   Invariant: input hints are a subset of output hints
inferInvariants :: Expr -> Step -> Verify Step
inferInvariants prefix step@Step {lhs, hints, rhs}
  | Q.elemPartial NoInfer hints = return step
  | otherwise = do
    (_, prefixCtx, _) <- Q.singleResult <$> Q.symEval (prefix, Q.emptyCtx, [])
    (VRef addrL, ctxL, _) <- Q.singleResult <$> Q.symEval (lhs, prefixCtx, [])
    (VRef addrR, ctxR, _) <- Q.singleResult <$> Q.symEval (rhs, prefixCtx, [])
    let comVars = commonVars [] addrL ctxL addrR ctxR
    Q.debug $ "Inferred equality invariants on fields: " ++ ppVars comVars
    return $ step {hints = hints ++ map Q.fieldEqual comVars}
  where
    ppVars :: [[Var]] -> String
    ppVars = L.intercalate ", " . map (L.intercalate ".")
    commonVars :: [Var] -> Addr -> Context -> Addr -> Context -> [[Var]]
    commonVars prefixFields addrL ctxL addrR ctxR
      | Just objL <- ctxL ^. Q.ctxObjs . Lens.at addrL
      , Just objR <- ctxR ^. Q.ctxObjs . Lens.at addrR =
        let localsL = objL ^. Q.objLocals
            common =
              M.filterWithKey
                (\fieldL locL ->
                   case objR ^. Q.objLocals . Lens.at fieldL of
                     Just locR ->
                       (locL ^. Q.localType) == (locR ^. Q.localType) &&
                       not (locL ^. Q.localImmutable) &&
                       not (locR ^. Q.localImmutable) &&
                       (locL ^. Q.localValue) ==
                       (locR ^. Q.localValue)
                     _ -> False)
                localsL
            commonObjs =
              M.mapWithKey
                (\field locL ->
                   case ( locL ^. Q.localValue
                        , objR ^? Q.objLocals . Lens.ix field . Q.localValue) of
                     (VRef aL, Just (VRef aR)) -> Just (field, aL, aR)
                     _ -> Nothing)
                localsL
         in map (\field -> prefixFields ++ [field]) (M.keys common) ++
            (L.concatMap
               (\(field, aL, aR) ->
                  commonVars (prefixFields ++ [field]) aL ctxL aR ctxR) .
             Maybe.catMaybes .
             M.elems $
             commonObjs)
      | otherwise = error "commonVars called with invalid addresses"

-- | Return the number of remaining verification conditions
proveStep :: Expr -> Step -> Verify Int
proveStep prefix step = do
  Q.debug $ "---------------------------\nVerifying step: " ++ stepNote step
  remaining <- checkEqv prefix step
  return $ L.sum (map (L.length . snd) remaining)
