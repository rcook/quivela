-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module Quivela.SymEval
    -- * VerifyEnv
  ( VerifyEnv
  , cacheFile
  , debugFlag
  , jobName
  , jobNote
  , jobStep
  , tempDir
  , writeAllVCsToFile
  , emptyVerifyEnv
    -- * VerifyState
  , VerifyState
  , alreadyVerified
  , tempFiles
  , verifyPrefixCtx
  , z3Proc
  , newVerifyState
    -- * Verify
  , Verify
  , debug
  , freshVar
  , onlySimpleTypes
  , runVerify
  , useCache
    -- * Symbolic evaluation
  , symArgs
  , symEval
  ) where

import qualified Control.Conditional as Cond
import qualified Control.Lens as Lens
import Control.Lens ((%=), (.~), (?~), (^.), (^?))
import Control.Monad.Fail (MonadFail)
import qualified Control.Monad.RWS.Strict as Monad
import qualified Control.Monad.RWS.Strict as RWS
import Control.Monad.RWS.Strict (MonadIO, MonadReader, MonadState, RWST)
import qualified Data.ByteString as ByteString
import qualified Data.Generics as Generics
import qualified Data.List as L
import Data.List ((!!))
import qualified Data.Map as M
import qualified Data.Maybe as Maybe
import qualified Data.Serialize as Serialize
import qualified Data.Set as S
import qualified Quivela.Language as Q
import Quivela.Language
  ( Addr
  , Config
  , Context
  , Expr(..)
  , Field(..)
  , FunDecl(..)
  , Local(..)
  , Method(..)
  , Object(..)
  , PathCond
  , PathCtx
  , Place(..)
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
import qualified Quivela.Util as Q
import qualified Quivela.Z3 as Q
import qualified System.Directory as Directory
import qualified System.IO as IO
import System.IO (Handle)
import qualified System.Process as Proc
import System.Process (ProcessHandle)

-- ----------------------------------------------------------------------------
-- Pure type inference
-- ----------------------------------------------------------------------------
--
-- The inference is pure in the sense that it does not use the ambient environment
-- or state introduced later.  There are two methods:
--   - typeOfX
--   - XHasType
-- where X ∈ {Value, SymValue}.
-- | Infer type of a symbolic value. Will return 'TAny' for most operations
-- except plain variables and inserting into a well-typed map.
typeOfSymValue :: Context -> SymValue -> Type
typeOfSymValue _ (SymVar _ t) = t
typeOfSymValue _ (Proj _ _) = TAny
  -- we could have more precise type information here if the idx was constant
typeOfSymValue ctx (Insert key val m)
  | TMap tk tv <- typeOfValue ctx m =
    let tk' =
          if typeOfValue ctx key == tk
            then tk
            else TAny
        tv' =
          if typeOfValue ctx val == tv
            then tv
            else TAny
     in TMap tk' tv'
  | otherwise = TMap (typeOfValue ctx key) (typeOfValue ctx val)
      -- Insert always turns 'map' into an actual TMap
typeOfSymValue _ (Lookup _ _) = TAny
  -- we don't know if idx is going to be in the map, so
  -- we can't give more precise type information here.
typeOfSymValue _ctx (AdversaryCall _) = TAny
typeOfSymValue ctx (Add v1 v2)
  | typeOfValue ctx v1 == TInt && typeOfValue ctx v2 == TInt = TInt
  | otherwise = TAny
typeOfSymValue ctx (Ref a)
  -- If the reference points to an object, use that object's type of the reference
  -- schoepe@: I'm not sure if we shouldn't instead distinguish between a reference to a typed
  -- object and that typed object instead on the type level.
  | Just obj <- ctx ^. Q.ctxObjs . Lens.at a = obj ^. Q.objType
  | otherwise = TAny
typeOfSymValue _ctx (Call _ _) = TAny
typeOfSymValue _ctx v = error $ "Not implemented: typeOfSymValue: " ++ show v

-- | Infer the type of a value. 'TAny' is returned when the inference can't
-- figure out anything more precise.
typeOfValue :: Context -> Value -> Type
typeOfValue _ (VInt 0) = TAny
typeOfValue _ (VInt _) = TInt
typeOfValue _ VNil = TAny
typeOfValue ctx (Sym sv) = typeOfSymValue ctx sv
typeOfValue ctx (VTuple vs) = TTuple $ map (typeOfValue ctx) vs
typeOfValue ctx (VSet vs) = TSet tv
  where
    valueTypes = map (typeOfValue ctx) . S.elems $ vs
    tv
      | [t] <- L.nub valueTypes = t
      | otherwise = TAny
typeOfValue ctx (VMap vs) = TMap tk tv
  where
    keyTypes = map (typeOfValue ctx) $ M.keys vs
    valueTypes = map (typeOfValue ctx) $ M.elems vs
    tk
      | [t] <- L.nub keyTypes = t -- all keys have same type
      | otherwise = TAny
    tv
      | [t] <- L.nub valueTypes = t
      | otherwise = TAny

-- | Check whether value has given type.
valueHasType :: Context -> Value -> Type -> Bool
valueHasType _ _ TAny = True
valueHasType _ (VInt 0) (TMap _ _) = True
valueHasType _ (VInt _) TInt = True
valueHasType ctx (VTuple vs) (TTuple ts)
  | L.length vs == L.length ts =
    L.all (uncurry (valueHasType ctx)) (L.zip vs ts)
  | otherwise = False
valueHasType ctx (VMap values) (TMap tk tv) =
  L.all (\key -> valueHasType ctx key tk) (M.keys values) &&
  L.all (\val -> valueHasType ctx val tv) (M.elems values)
valueHasType ctx (Sym sv) t = symValueHasType ctx sv t
valueHasType _ _ _ = False

-- | Check if symbolic value has a given type.
symValueHasType :: Context -> SymValue -> Type -> Bool
symValueHasType _ _ TAny = True
symValueHasType ctx (Add e1 e2) TInt =
  valueHasType ctx e1 TInt && valueHasType ctx e2 TInt
symValueHasType _ (SymVar _ t') t = t == t'
symValueHasType ctx (Ref a) t
  | Just t' <- ctx ^? Q.ctxObjs . Lens.ix a . Q.objType = t == t'
symValueHasType ctx (Insert k v m) (TMap tk tv)
  -- TODO: this could be more precise: if we know that m is definitely not
  -- a map at this point, we can return True if k has type tk and v has type tv
  -- we should call the solver to check if this is the case to figure this out.
 = do
  L.and
    [ valueHasType ctx k tk
    , valueHasType ctx v tv
    , valueHasType ctx m (TMap tk tv)
    ]
symValueHasType _ _ _ = False

-- ----------------------------------------------------------------------------
-- The Verify Monad.
-- ----------------------------------------------------------------------------
--
-- The monad is simply a newtype around RWST with custom read-only environment
-- and read-write state.  The inner monad is IO, as we are constantly
-- communicating with Z3 over a pipe.
-- | The fixed environment for symbolic evaluation.
data VerifyEnv = VerifyEnv
  { _cacheFile :: Maybe FilePath
    -- ^ Proof cache location
  , _debugFlag :: Bool
    -- ^ print debugging information
  , _jobName :: String
  , _jobNote :: String
  , _jobStep :: Int
  , _splitEq :: Bool
  , _tempDir :: Maybe FilePath
    -- ^ Split == operator into two paths during symbolic evaluation?
  , _writeAllVCsToFile :: Bool
    -- ^ For debugging, write all VCs to file, even if they succeed
  }

emptyVerifyEnv :: VerifyEnv
emptyVerifyEnv =
  VerifyEnv
    { _cacheFile = Nothing
    , _debugFlag = True
    , _jobName = "quivela"
    , _jobNote = "no-note"
    , _jobStep = 0
    , _splitEq = False
    , _tempDir = Nothing
    , _writeAllVCsToFile = False
    }

Lens.makeLenses ''VerifyEnv

data VerifyState = VerifyState
  { _alreadyVerified :: Set (Expr, Expr)
    -- ^ A cache of steps that we already verified before
    -- FIXME: Currently, we cannot serialize invariants, since they include functions as arguments
    -- in some cases
  , _nextVar :: Map String Integer
    -- ^ Map of already used integers for fresh variable prefix
  , _tempFiles :: Int
  , _verifyPrefixCtx :: Context
    -- ^ The context returned by the "prefix" program of a proof that defines constructors,
    -- lists assumptions, etc.
  , _z3Proc :: (Handle, Handle, ProcessHandle)
    -- ^ For performance reasons, we spawn a Z3 process once and keep it around
  }

Lens.makeLenses ''VerifyState

-- | Return an initial state for the verifier monad
newVerifyState :: VerifyEnv -> IO VerifyState
newVerifyState env = do
  (Just hin, Just hout, _, procHandle) <-
    Proc.createProcess $
    (Proc.proc "z3" ["-in"])
      { Proc.std_out = Proc.CreatePipe
      , Proc.std_in = Proc.CreatePipe
      , Proc.std_err = Proc.CreatePipe
      }
  IO.hSetBuffering hin IO.NoBuffering
  IO.hSetBuffering hout IO.NoBuffering
  IO.hPutStrLn hin $ Q.renderCommands Q.prelude
  verificationCache <-
    case _cacheFile env of
      Nothing -> return S.empty
      Just f -> do
        exists <- Directory.doesFileExist f
        if not exists
          then return S.empty
          else do
            maybeCache <-
              Serialize.decode <$> Monad.liftIO (ByteString.readFile f)
            case maybeCache of
              Right cache -> return cache
              Left _ -> error $ "Can't parse proof cache: " ++ f
  return
    VerifyState
      { _alreadyVerified = verificationCache
      , _nextVar = M.empty
      , _tempFiles = 0
      , _verifyPrefixCtx = Q.emptyCtx
      , _z3Proc = (hin, hout, procHandle)
      }

-- | A monad for generating and discharging verification conditions, which
-- allows generating free variables and calling external solvers.
newtype Verify a = Verify
  { unVerify :: RWST VerifyEnv () VerifyState IO a
  } deriving ( Monad
             , MonadFail
             , MonadState VerifyState
             , MonadIO
             , Applicative
             , Functor
             , MonadReader VerifyEnv
             )

-- | Run a Verify action
runVerify :: VerifyEnv -> Verify a -> IO a
runVerify env action = do
  initState <- newVerifyState env
  (res, _, ()) <- Monad.runRWST (unVerify action) env initState
  return res

useCache :: Verify Bool
useCache = (Maybe.isJust . _cacheFile) <$> RWS.ask

debug :: String -> Verify ()
debug msg =
  Cond.ifM (Lens.view debugFlag) (RWS.liftIO (putStrLn msg)) (return ())

-- | Generate a fresh variable starting with a given prefix
freshVar :: String -> Verify String
freshVar prefix = do
  last <- Lens.use (nextVar . Lens.at prefix)
  case last of
    Just n -> do
      nextVar . Lens.ix prefix %= (+ 1)
      return $ "?" ++ prefix ++ show n
    Nothing -> do
      RWS.modify (nextVar . Lens.at prefix ?~ 0)
      freshVar prefix

onlySimpleTypes :: Data p => p -> Verify ()
onlySimpleTypes x =
  Monad.unless
    (L.null .
     Generics.listify
       (\case
          TNamed _ -> True
          _ -> False) $
     x)
    (error $ "Symbolic objects as method arguments not yet supported")

-- ----------------------------------------------------------------------------
-- Variables
-- ----------------------------------------------------------------------------
-- | Find the location of a variable in the context. Since this may have to add
-- a location for the variable in the scope or as a local, we also return an
-- updated context to use with the returned 'Place'. The 'Bool' component of the
-- result indicates if the context had to be modified.
findVar :: Var -> Context -> (Place, Context, Bool)
findVar x ctx
  | Just (_, t) <- M.lookup x (ctx ^. Q.ctxScope) =
    ( Place
        { _placeLens = Q.ctxScope . Lens.ix x . Lens._1
        , _placeConst = False
        , _placeType = t
        }
    , ctx
    , False)
  | Just loc <-
     ctx ^? Q.ctxObjs . Lens.ix (ctx ^. Q.ctxThis) . Q.objLocals . Lens.ix x =
    ( Place
        { _placeLens =
            Q.ctxObjs . Lens.ix (ctx ^. Q.ctxThis) . Q.objLocals . Lens.ix x .
            Q.localValue
        , _placeConst = loc ^. Q.localImmutable
        , _placeType = loc ^. Q.localType
        }
    , ctx
    , False)
  -- the variable doesn't exist yet, so we need to create it:
  -- if we're not in a global context, we use a local variable
  -- FIXME: this should probably check if we are inside a method instead, but currently
  -- we don't store whether this is the case in the context.
  | ctx ^. Q.ctxThis /= 0 =
    ( Place
        { _placeLens = Q.ctxScope . Lens.ix x . Lens._1
        , _placeConst = False
        , _placeType = TAny
        }
    , Lens.set (Q.ctxScope . Lens.at x) (Just (Q.defaultValue, TAny)) ctx
    , True)
  | otherwise =
    ( Place
        { _placeLens =
            Q.ctxObjs . Lens.ix 0 . Q.objLocals . Lens.ix x . Q.localValue
        , _placeConst = False
        , _placeType = TAny
        }
    , Lens.set
        (Q.ctxObjs . Lens.ix 0 . Q.objLocals . Lens.at x)
        (Just (Local Q.defaultValue TAny False))
        ctx
    , True)

-- ----------------------------------------------------------------------------
-- LValues
-- ----------------------------------------------------------------------------
-- | Find or create the place of a valid l-value expression (i.e. a variable,
-- a projection, or an indexing expression with an l-value to the left of the [.
-- The result value has the same structure as the result of 'findVar', except
-- for an added path condition component.
findLValue ::
     Expr
  -> Context
  -> PathCond
  -> Verify [Maybe (Place, Context, PathCond, Bool)]
findLValue (EVar x) ctx pathCond =
  return
    [ Just $
      (\(place, ctx', created) -> (place, ctx', pathCond, created))
        (findVar x ctx)
    ]
findLValue (EProj obj name) ctx pathCond = do
  Q.foreachM (symEval (obj, ctx, pathCond)) $ \case
    (VRef addr, ctx', pathCond')
      | Just loc <-
         ctx' ^? Q.ctxObjs . Lens.ix addr . Q.objLocals . Lens.ix name ->
        return
          [ Just
              ( Place
                  { _placeLens =
                      Q.ctxObjs . Lens.ix addr . Q.objLocals . Lens.ix name .
                      Q.localValue
                  , _placeConst = loc ^. Q.localImmutable
                  , _placeType = loc ^. Q.localType
                  }
              , ctx'
              , pathCond'
              , False -- TODO: Are we sure about False here if ctx != ctx'?
               )
          ]
    _ -> return [Nothing]
findLValue expr@(EIdx obj idx) ctx pathCond =
  Q.foreachM (findLValue obj ctx pathCond) $ \case
    Nothing -> error $ "Invalid l-value: " ++ show expr
    Just (place, ctx', pathCond', _created) ->
      Q.foreachM (symEval (idx, ctx', pathCond')) $ \(idxVal, ctx'', pathCond'') ->
        case ctx'' ^? (place ^. Q.placeLens) of
          Just (VMap m) ->
            case M.lookup idxVal m of
              Just _ ->
                return
                  [ Just
                      ( Place
                          { _placeLens =
                              (place ^. Q.placeLens) . Q.valMap . Lens.ix idxVal
                          , _placeType = TAny -- FIXME: Put the map value type here
                          , _placeConst = False
                          }
                      , ctx''
                      , pathCond''
                      , False)
                  ]
              -- need to add the element to the map first to create a well-typed lens into it:
              -- this is because we use 'ix' instead of 'at' to access map elements, so the
              -- interface is the same as for lenses to an ordinary variable
              _ ->
                return
                  [ Just
                      ( Place
                          { _placeLens =
                              (place ^. Q.placeLens) . Q.valMap . Lens.ix idxVal
                          , _placeType = TAny -- FIXME: Put the map value type here
                          , _placeConst = False
                          }
                      , Lens.set
                          ((place ^. Q.placeLens) . Q.valMap . Lens.at idxVal)
                          (Just Q.defaultValue)
                          ctx''
                      , pathCond''
                      , True)
                  ]
          Just (Sym _) ->
            return
              [ Just
                  ( Place
                      { _placeLens =
                          (place ^. Q.placeLens) . Q.symVal . Lens.ix idxVal
                      , _placeType = TAny
                      , _placeConst = False
                      }
                  , ctx''
                  , pathCond''
                  , False)
              ]
          -- Not a map yet, create one:
          _ ->
            return
              [ Just
                  ( Place
                      { _placeLens =
                          (place ^. Q.placeLens) . Q.valMap . Lens.ix idxVal
                      , _placeType = TAny -- FIXME: Put the map value type here
                      , _placeConst = False
                      }
                  , Lens.set
                      (place ^. Q.placeLens)
                      (VMap $ M.fromList [(idxVal, Q.defaultValue)])
                      ctx''
                  , pathCond''
                  , True)
              ]
findLValue expr _ _ = error $ "invalid l-value: " ++ show expr

-- ----------------------------------------------------------------------------
-- Symbolic evaluation
-- ----------------------------------------------------------------------------
symEval :: Config -> Verify Results
symEval (ENop, ctx, pathCond) = return [(VNil, ctx, pathCond)]
symEval (EConst v, ctx, pathCond) = return [(v, ctx, pathCond)]
symEval (EVar x, ctx, pathCond) = return [(var, ctx, pathCond)]
  where
    var
      | (place, ctx', _) <- findVar x ctx
      , Just v <- ctx' ^? (place ^. Q.placeLens) = v
      | otherwise = evalError ("No such variable: " ++ x) ctx
symEval (ETuple es, ctx, pathCond) =
  Q.foreachM (symEvalList (es, ctx, pathCond)) $ \(vs, ctx', pathCond') ->
    return [(VTuple vs, ctx', pathCond')]
symEval (ETupleProj etup eidx, ctx, pathCond) =
  Q.foreachM (symEval (etup, ctx, pathCond)) $ \(vtup, ctx', pathCond') ->
    Q.foreachM (symEval (eidx, ctx', pathCond')) $ \(vidx, ctx'', pathCond'') ->
      return [(lookupInTuple vtup vidx, ctx'', pathCond'')]
  where
    lookupInTuple :: Value -> Value -> Value
    lookupInTuple (VTuple vs) (VInt i)
      | fromInteger i < L.length vs = vs !! fromInteger i
      | otherwise = error "Invalid tuple index"
    lookupInTuple tup i@(Sym _) = Sym (Proj tup i)
    lookupInTuple tup@(Sym _) i = Sym (Proj tup i)
    lookupInTuple _ _ = error "Invalid tuple lookup"
symEval (EProj obj name, ctx, pathCond) =
  Q.foreachM (symEval (obj, ctx, pathCond)) $ \(val, ctx', pathCond') ->
    case val of
      VRef addr
        | Just loc <-
           ctx' ^? Q.ctxObjs . Lens.ix addr . Q.objLocals . Lens.ix name ->
          return [(loc ^. Q.localValue, ctx', pathCond')]
      Sym sv
        -- we might be able to make progress from here by forcing
        -- the receiver value to something more concrete:
       -> do
        forced <- force (Sym sv, ctx, pathCond)
        if forced == [(val, ctx', pathCond')]
          then return [(Sym (Deref val name), ctx', pathCond')]
          else Q.foreachM (pure forced) $ \(val', ctx'', pathCond'') -> do
                 symEval (EProj (EConst val') name, ctx'', pathCond'')
      _ -> return [(Sym (Deref val name), ctx', pathCond')]
symEval (EIdx base idx, ctx, pathCond) =
  Q.foreachM (symEval (base, ctx, pathCond)) $ \(baseVal, ctx', pathCond') ->
    Q.foreachM (symEval (idx, ctx', pathCond')) $ \(idxVal, ctx'', pathCond'') ->
      case baseVal of
        VInt 0 -> return [(VInt 0, ctx'', pathCond'')] -- 0 is the empty map
        VMap vals ->
          if Q.isSym idxVal
            then return [(Sym (Lookup idxVal baseVal), ctx'', pathCond'')]
            else case M.lookup idxVal vals of
                   Just val -> return [(val, ctx'', pathCond'')]
                   Nothing -- if we can't find the value in the map, keep the lookup symbolic:
                    ->
                     if Q.isSym idxVal
                       then return
                              [(Sym (Lookup idxVal baseVal), ctx'', pathCond'')]
                       else return [((VInt 0), ctx'', pathCond'')]
        Sym _ -> return [(Sym (Lookup idxVal baseVal), ctx'', pathCond'')]
        _ -> return [((VInt 0), ctx'', pathCond'')]
symEval (EAssign (ETuple pat) rhs, ctx, pathCond)
  -- Evaluate a pattern-match expression with list of variables on LHS and another expression
  -- on the right-hand side. This corresponds to writing @<x1, .., xn> = rhs@. Currently,
  -- this does not support nested patterns.
  -- check that all elements of the pattern are just simple variables
  | Just vars <-
     Monad.sequence $
     map
       (\case
          EVar x -> Just x
          _ -> Nothing)
       pat =
    Q.foreachM (symEval (rhs, ctx, pathCond)) $ \(vrhs, _ctx', _pathCond') ->
      let (lvalues, ctx'') =
            L.foldr
              (\var (places, cx) ->
                 case findVar var cx of
                   (place, cx', _) -> (place : places, cx'))
              ([], ctx)
              vars
          (rhsVals, projEq) =
            case vrhs of
              Sym _ ->
                ( map
                    (Sym . Proj vrhs . VInt . fromIntegral)
                    [0 .. L.length pat - 1]
                , [vrhs :=: VTuple rhsVals])
              VTuple rhsVals'
                | L.length rhsVals' == L.length vars -> (rhsVals', [])
              _ ->
                error $ "Invalid concrete value for pattern-match expression: " ++
                show (pat, rhs, vrhs)
          ctx''' =
            L.foldr
              (\(place, proj) cx -> Lens.set (place ^. Q.placeLens) proj cx)
              ctx''
              (L.zip lvalues rhsVals)
       in return [(vrhs, ctx''', projEq ++ pathCond)]
  | otherwise =
    error $ "Nested patterns not supported yet: " ++ show pat ++ " = " ++
    show rhs
symEval (EAssign lhs rhs, ctx, pathCond) =
  Q.foreachM (symEval (rhs, ctx, pathCond)) $ \(rhsVal, ctx', pathCond') ->
    Q.foreachM (findLValue lhs ctx' pathCond') $ \case
      Just (place, ctx'', pathCond'', _) -> do
        Cond.unless (valueHasType ctx'' rhsVal (place ^. Q.placeType)) $ do
          error $ "Ill-typed assignment from value of type: " ++
            show (typeOfValue ctx'' rhsVal) ++
            " to place with type: " ++
            show (place ^. Q.placeType)
        Cond.when (place ^. Q.placeConst) $ do
          error $ "Assignment to constant location: " ++ show lhs
        return
          [(rhsVal, Lens.set (place ^. Q.placeLens) rhsVal ctx'', pathCond'')]
      _ -> error $ "Invalid l-value: " ++ show lhs
symEval (EIf cnd thn els, ctx, pathCond) = do
  Q.foreachM (symEval (cnd, ctx, pathCond)) handle
  where
    handle (cndVal, c, p)
      | Q.isSym cndVal = do
        thnPaths <- symEval (thn, c, Not (cndVal :=: VInt 0) : p)
        elsPaths <- symEval (els, c, cndVal :=: VInt 0 : p)
        return $ thnPaths ++ elsPaths
      | cndVal == VInt 0 = symEval (els, c, p)
      | otherwise = symEval (thn, c, p)
symEval (ESeq e1 e2, ctx, pathCond) = do
  Q.foreachM (symEval (e1, ctx, pathCond)) $ \(_, ctx', pathCond') ->
    symEval (e2, ctx', pathCond')
symEval (EMethod m, ctx, pathCond) =
  let ctx'
        | Just _ <- ctx ^? Q.ctxObjs . Lens.at (ctx ^. Q.ctxThis) =
          Q.ctxObjs . Lens.ix (ctx ^. Q.ctxThis) . Q.objMethods .
          Lens.at (m ^. Q.methodName) ?~
          m $
          ctx
        | otherwise = error "failed to define method"
   in return [(VNil, ctx', pathCond)]
symEval (ECall (EConst VNil) "++" [lval], ctx, pathCond) = do
  Q.foreachM (findLValue lval ctx pathCond) $ \case
    Just (place, ctx', pathCond', False)
      | Just oldVal <- ctx' ^? (place ^. Q.placeLens) -> do
        updPaths <-
          symEval
            ( EAssign lval (ECall (EConst VNil) "+" [lval, EConst (VInt 1)])
            , ctx'
            , pathCond')
        return $ map (\(_, c, p) -> (oldVal, c, p)) updPaths
    _ -> error $ "Invalid l-value in post-increment: " ++ show lval
symEval (ECall (EConst VNil) op [lval], ctx, pathCond) | op == Q.prefixIncrOp = do
  Q.foreachM (findLValue lval ctx pathCond) $ \case
    Just (_, ctx', pathCond', False) ->
      symEval
      ( EAssign lval (ECall (EConst VNil) "+" [lval, EConst (VInt 1)])
      , ctx'
      , pathCond')
    _ -> error $ "Invalid l-value in pre-increment: " ++ show lval
symEval (ECall (EConst VNil) "==" [e1, e2], ctx, pathCond) =
  Q.foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    Q.foreachM (symEval (e2, ctx', pathCond')) $ \(v2, ctx'', pathCond'') -> do
      doSplit <- Lens.view splitEq
      if (Q.isSym v1 || Q.isSym v2) && (v1 /= v2)
        then if doSplit
               then return
                      [ (VInt 0, ctx'', Not (v1 :=: v2) : pathCond'')
                      , (VInt 1, ctx'', v1 :=: v2 : pathCond'')
                      ]
               else return
                      [ ( Sym (ITE (v1 :=: v2) (VInt 1) (VInt 0))
                        , ctx''
                        , pathCond'')
                      ]
        else if v1 == v2 -- FIXME: Is this sound?  If the values are Haskell-equal, 1 makes sense, but it's not obvious to me that non-Haskell-equal values are definitely not Quivela-equal.
               then return [(VInt 1, ctx'', pathCond'')]
               else return [(VInt 0, ctx'', pathCond'')]
symEval (ECall (EConst VNil) "!=" [e1, e2], ctx, pathCond) =
  symEval (ECall (EConst VNil) "!" [ECall (EConst VNil) "==" [e1, e2]], ctx, pathCond)
symEval (ECall (EConst VNil) "!" [e], ctx, pathCond) = do
  Q.foreachM (symEval (e, ctx, pathCond)) $ \(v, ctx', pathCond') ->
    case v of
      Sym _ ->
        return
          [ (VInt 1, ctx', v :=: VInt 0 : pathCond')
          , (VInt 0, ctx', Not (v :=: (VInt 0)) : pathCond')
          ]
      VInt 0 -> return [(VInt 1, ctx', pathCond')]
      _ -> return [((VInt 0), ctx', pathCond')]
symEval (ECall (EConst VNil) "&" [e1, e2], ctx, pathCond) = do
  Q.foreachM (symEval (e1, ctx, pathCond)) $ \case
    ((VInt 0), ctx', pathCond') -> return [((VInt 0), ctx', pathCond')]
    (v1, ctx', pathCond')
      | Q.isSym v1
      -- TODO: ask verifier if v can be proven to be 0/non-0
       -> do
        results <- symEval (e2, ctx', Not (v1 :=: VInt 0) : pathCond')
        return $ ((VInt 0), ctx', v1 :=: VInt 0 : pathCond') : results
    (_, ctx', pathCond') -> symEval (e2, ctx', pathCond')
symEval (ECall (EConst VNil) "|" [e1, e2], ctx, pathCond) = do
  Q.foreachM (symEval (e1, ctx, pathCond)) $ \case
    ((VInt 0), ctx', pathCond') -> symEval (e2, ctx', pathCond')
    (v1, ctx', pathCond')
      | Q.isSym v1 -> do
        results <- symEval (e2, ctx', (v1 :=: VInt 0) : pathCond')
        return $ (v1, ctx', Not (v1 :=: VInt 0) : pathCond') : results
    (v, ctx', pathCond') -> return [(v, ctx', pathCond')]
symEval (ECall (EConst VNil) "adversary" [], ctx, pathCond) =
  return
    [ ( VRef (Q.nextAddr ctx)
      , Q.ctxObjs . Lens.at (Q.nextAddr ctx) ?~ Q.adversary $ ctx
      , pathCond)
    ]
symEval (ECall obj name args, ctx, pathCond) =
  Q.foreachM (symEval (obj, ctx, pathCond)) $ \(vobj, ctx', pathCond') ->
    Q.foreachM (symEvalList (args, ctx', pathCond')) $ \(evaledArgs, ctx'', pathCond'') ->
      symEvalCall vobj name (evaledArgs, ctx'', pathCond'')
symEval (ENew fields body, ctx, pathCond) =
  Q.foreachM (symEvalFields (fields, ctx, pathCond)) $ \(locals, ctx', pathCond') ->
    let next = Q.nextAddr ctx'
        ctx'' =
          Q.ctxObjs . Lens.at next ?~ Q.emptyObject {_objLocals = locals} $ ctx'
        ctx''' = Lens.set Q.ctxThis next ctx''
     in Q.foreachM (symEval (body, ctx''', pathCond')) $ \(_, ctx'''', pathCond'') ->
          return
            [ ( VRef next
              , Lens.set Q.ctxThis (ctx' ^. Q.ctxThis) ctx''''
              , pathCond'')
            ]
symEval (tdecl@(ETypeDecl name _ _ _), ctx, pathCond)
  | L.elem name $ M.keys (ctx ^. Q.ctxTypeDecls) =
    error $ "Duplicate type declaration: " ++ name
  | otherwise =
    return [(VNil, Q.ctxTypeDecls . Lens.at name ?~ tdecl $ ctx, pathCond)]
symEval (expr@(ENewConstr typeName args), ctx, pathCond)
  | Just tdecl <- ctx ^. Q.ctxTypeDecls . Lens.at typeName
      -- evaluate new expression stored for the type, then set the object's type
      -- to keep track that this was constructed with a constructor
   = do
    Cond.unless
      (map fst args == map (\(name, _, _) -> name) (tdecl ^. Q.typedeclFormals)) $
      (error $ "Mismatch between actual and expected constructor arguments: " ++
       show expr)
    let fields =
          L.zipWith
            (\(name, e) (_, immut, typ) ->
               Field
                 { _fieldName = name
                 , _fieldInit = e
                 , _immutable = immut
                 , _fieldType = typ
                 })
            args
            (tdecl ^. Q.typedeclFormals) ++
          map
            (\(name, val) ->
               Field
                 { _fieldName = name
                 , _fieldInit = EConst val
                 , _immutable = False -- FIXME:
                 , _fieldType = typeOfValue ctx val
                 })
            (tdecl ^. Q.typedeclValues)
    Q.foreachM
      (symEval
         (ENew fields (Maybe.fromJust $ tdecl ^? Q.typedeclBody), ctx, pathCond)) $ \(val, ctx', pathCond') ->
      case val of
        VRef addr ->
          return
            [ ( val
              , Q.ctxObjs . Lens.ix addr . Q.objType .~ TNamed typeName $ ctx'
              , pathCond')
            ]
        _ -> return [(val, ctx', pathCond')] -- schoepe@: object creation may have returned 0.  FIXME: Check this
  | otherwise = error $ "No such type: " ++ typeName
symEval (ESetCompr x v e, ctx, pathCond)
  -- Get new symbolic variable for variable bound by comprehension:
 = do
  fv <- freshVar x
  let fvExpr = Sym $ SymVar fv TAny
  -- Bind name in new context, in which we can evaluate predicate
  -- and function expression of comprehension
  let ctx' = Lens.over Q.ctxScope (M.insert x (fvExpr, TAny)) ctx
  comprs <-
    Q.foreachM (symEval (e, ctx', pathCond)) $ \(predVal, _, pathCond') ->
      Q.foreachM (symEval (v, ctx', pathCond')) $ \(funVal, _, pathCond'') -> do
        return
          [ Sym
              (SetCompr
                 fv
                 funVal
                 (Q.conjunction $ Not (predVal :=: VInt 0) : pathCond''))
          ]
  return
    [(L.foldr (\m k -> Sym (Q.Union m k)) (VSet S.empty) comprs, ctx, pathCond)]
symEval (EMapCompr x v e, ctx, pathCond) = do
  fv <- freshVar x
  let fvExpr = Sym $ SymVar fv TAny
  let ctx' = Lens.over Q.ctxScope (M.insert x (fvExpr, TAny)) ctx
  comprs <-
    Q.foreachM (symEval (e, ctx', pathCond)) $ \(predVal, _, pathCond') ->
      Q.foreachM (symEval (v, ctx', pathCond')) $ \(funVal, _, pathCond'') -> do
        return
          [ Sym
              (MapCompr
                 fv
                 funVal
                 (Q.conjunction $ Not (predVal :=: VInt 0) : pathCond''))
          ]
  return
    [ ( L.foldr (\m k -> Sym $ MapUnion m k) (VMap M.empty) comprs
      , ctx
      , pathCond)
    ]
symEval (EIn elt s, ctx, pathCond) = do
  Q.foreachM (symEval (elt, ctx, pathCond)) $ \(velt, ctx', pathCond') ->
    Q.foreachM (symEval (s, ctx', pathCond')) $ \(vset, ctx'', pathCond'') -> do
      if (Q.isSym velt || Q.isSym vset)
        then return [(Sym (In velt vset), ctx'', pathCond'')]
        else case vset of
               VSet vals ->
                 (if velt `S.member` vals
                    then return [(VInt 1, ctx'', pathCond'')]
                    else return [(VInt 0, ctx'', pathCond'')])
               _ ->
                 error $
                 "Tried to test for set membership in concrete non-set value: " ++
                 show vset
symEval (ESubmap e1 e2, ctx, pathCond) = do
  Q.foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    Q.foreachM (symEval (e2, ctx', pathCond')) $ \(v2, ctx'', pathCond'') -> do
      if Q.isSym v1 || Q.isSym v2
        then return [(Sym (Submap v1 v2), ctx'', pathCond'')]
        else case (v1, v2) of
               (VMap m1, VMap m2) ->
                 if (S.fromList (M.keys m1) `S.isSubsetOf`
                     S.fromList (M.keys m2))
                   then return [(VInt 1, ctx'', pathCond'')]
                   else return [(VInt 0, ctx'', pathCond'')]
               _ ->
                 error $ "Concrete non-map arguments for ⊆ operator: " ++
                 show (v1, v2)
symEval (EAssume e1 e2, ctx, pathCond) =
  return [(VNil, Lens.over Q.ctxAssumptions ((e1, e2) :) ctx, pathCond)]
symEval (EAssert p, ctx, pathCond) =
  return [(VNil, Lens.over Q.ctxAssertions (p :) ctx, pathCond)]
symEval (funDecl@EFunDecl {}, ctx, pathCond) =
  let funName = funDecl ^. Q.efunDeclName
   in return
        [ ( VNil
          , Lens.over
              Q.ctxFunDecls
              (M.insert funName (FunDecl funName (funDecl ^. Q.efunDeclArgs)))
              ctx
          , pathCond)
        ]
symEval (EUnion e1 e2, ctx, pathCond) = do
  Q.foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    Q.foreachM (symEval (e2, ctx', pathCond')) $ \(v2, ctx'', pathCond'') -> do
      if (Q.isSym v1 || Q.isSym v2)
        then return [(Sym (Union v1 v2), ctx'', pathCond'')]
        else case (v1, v2) of
               (VSet vals1, VSet vals2) ->
                 return [(VSet (vals1 `S.union` vals2), ctx'', pathCond'')]
               _ ->
                 error $ "Tried to union non-set values: " ++ show v1 ++ " ∪ " ++
                 show v2
symEval (EIntersect e1 e2, ctx, pathCond) = do
  Q.foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    Q.foreachM (symEval (e2, ctx', pathCond')) $ \(v2, ctx'', pathCond'') -> do
      if (Q.isSym v1 || Q.isSym v2)
        then return [(Sym (Intersect v1 v2), ctx'', pathCond'')]
        else case (v1, v2) of
               (VSet vals1, VSet vals2) ->
                 return
                   [(VSet (vals1 `S.intersection` vals2), ctx'', pathCond'')]
               _ ->
                 error $ "Tried to union non-set values: " ++ show v1 ++ " ∪ " ++
                 show v2

symEvalList :: PathCtx [Expr] -> Verify [PathCtx [Value]]
symEvalList ([], ctx, pathCond) = return [([], ctx, pathCond)]
symEvalList (e:es, ctx, pathCond) =
  Q.foreachM (symEval (e, ctx, pathCond)) $ \(val, ctx', pathCond') ->
    Q.foreachM (symEvalList (es, ctx', pathCond')) $ \(evaledList, ctx'', pathCond'') ->
      return [(val : evaledList, ctx'', pathCond'')]

-- | Symbolically evaluate a list of field initializations in a given context and path condition
-- and return a list of possible executions of this list. Each element in the result is a list
-- of the same length where each field is evaluated, together with a context.
symEvalFields :: PathCtx [Field] -> Verify [PathCtx (Map Var Local)]
symEvalFields ([], ctx, pathCond) = return [(M.empty, ctx, pathCond)]
symEvalFields (f:fs, ctx, pathCond) =
  Q.foreachM (symEval (f ^. Q.fieldInit, ctx, pathCond)) $ \(fieldVal, ctx', pathCond') -> do
    Cond.unless (valueHasType ctx' fieldVal (f ^. Q.fieldType)) $ do
      error $ "Ill-typed argument for field initialization: " ++ show fieldVal ++
        " is not a subtype of " ++
        show (f ^. Q.fieldType)
    Q.foreachM (symEvalFields (fs, ctx', pathCond')) $ \(evaledFields, ctx'', pathCond'') ->
      return
        [ ( M.insert
              (f ^. Q.fieldName)
              (Local fieldVal (f ^. Q.fieldType) (f ^. Q.immutable))
              evaledFields
          , ctx''
          , pathCond'')
        ]

-- | `symEvalCall obj name args ...` symbolically evaluates a method call to method name on object obj
symEvalCall :: Value -> Var -> PathCtx [Value] -> Verify Results
symEvalCall (VRef addr) name (args, ctx, pathCond)
  | Just obj <- ctx ^. Q.ctxObjs . Lens.at addr
  , obj ^. Q.objAdversary =
    let newCalls = args : (ctx ^. Q.ctxAdvCalls)
     in return
          [ ( Sym (AdversaryCall newCalls)
            , Lens.set Q.ctxAdvCalls newCalls ctx
            , pathCond)
          ]
  | Just mtd <- Q.findMethod addr name ctx =
    callMethod addr mtd (args, ctx, pathCond)
  | otherwise =
    evalError
      ("Called non-existent method: " ++ name ++ "[" ++ show addr ++ "]")
      ctx
symEvalCall VNil "Z" ([m], ctx, pathCond) = return [(Sym (Z m), ctx, pathCond)]
symEvalCall VNil "rnd" ([], ctx, pathCond) =
  symEval (ENew [] ENop, ctx, pathCond)
symEvalCall VNil "+" ([arg1, arg2], ctx, pathCond)
  | Q.isSym arg1 || Q.isSym arg2 = return [(Sym (Add arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1
  , VInt m <- arg2 = return [(VInt (n + m), ctx, pathCond)]
  | otherwise =
    error $ "Addition of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "-" ([arg1, arg2], ctx, pathCond)
  | Q.isSym arg1 || Q.isSym arg2 = return [(Sym (Sub arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1
  , VInt m <- arg2 = return [(VInt (n - m), ctx, pathCond)]
  | otherwise =
    error $ "Subtraction of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "*" ([arg1, arg2], ctx, pathCond)
  | Q.isSym arg1 || Q.isSym arg2 = return [(Sym (Mul arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1
  , VInt m <- arg2 = return [(VInt (n * m), ctx, pathCond)]
  | otherwise =
    error $ "Multiplication of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "/" ([arg1, arg2], ctx, pathCond)
  | Q.isSym arg1 || Q.isSym arg2 = return [(Sym (Div arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1
  , VInt m <- arg2 =
    if m == 0
      then return [((VInt 0), ctx, pathCond)]
      else return [(VInt (n `div` m), ctx, pathCond)]
  | otherwise =
    error $ "Division of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "<" ([arg1, arg2], ctx, pathCond)
  | Q.isSym arg1 || Q.isSym arg2 = return [(Sym (Lt arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1
  , VInt m <- arg2 =
    return
      [ ( if n < m
            then VInt 1
            else VInt 0
        , ctx
        , pathCond)
      ]
  | otherwise =
    error $ "Comparison of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "<=" ([arg1, arg2], ctx, pathCond)
  | Q.isSym arg1 || Q.isSym arg2 = return [(Sym (Le arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1
  , VInt m <- arg2 =
    return
      [ ( if n <= m
            then VInt 1
            else VInt 0
        , ctx
        , pathCond)
      ]
  | otherwise =
    error $ "Comparison of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil name (args, ctx, pathCond)
  | Just mtd <- Q.findMethod (ctx ^. Q.ctxThis) name ctx =
    callMethod (ctx ^. Q.ctxThis) mtd (args, ctx, pathCond)
  | Just mtd <- Q.findMethod 0 name ctx = callMethod 0 mtd (args, ctx, pathCond)
  | Just funDecl <- ctx ^? Q.ctxFunDecls . Lens.ix name = do
    Cond.unless
      (L.length args == L.length (funDecl ^. Q.funDeclArgs))
      (error $ "Wrong number of arguments in call to uninterpreted function: " ++
       show (name, args))
    return [(Sym (Call name args), ctx, pathCond)]
  | otherwise = error $ "Call to non-existent method: " ++ name
symEvalCall (Sym sv) name (args, ctx, pathCond) = do
  forced <- force (Sym sv, ctx, pathCond)
  if forced == [(Sym sv, ctx, pathCond)]
    then do
      debug $ "Not implemented: calls on untyped symbolic objects: (" ++ show sv ++
        ")." ++
        name ++
        "(" ++
        show args ++
        ")"
       -- Return a fresh variable here to encode that we have no information about the returned value.
       -- FIXME: we should also havoc everything the base object may have access to.
       -- This case can still yield a provable verification condition if the path condition is contradictory
      fv <- freshVar "untyped_symcall"
      return [(Sym (SymVar fv TAny), ctx, pathCond)]
    else Q.foreachM (return forced) $ \(val, ctx', pathCond') -> do
           symEvalCall val name (args, ctx', pathCond')
symEvalCall (VInt 0) _ (_, ctx, pathCond) = return [((VInt 0), ctx, pathCond)]
symEvalCall obj name (_, ctx, _) =
  error $ "Bad method call[" ++ show obj ++ "]: " ++ name ++ "\n" ++ show ctx

-- ----------------------------------------------------------------------------
-- Util
-- ----------------------------------------------------------------------------
callMethod :: Addr -> Method -> PathCtx [Value] -> Verify Results
callMethod addr mtd (args, ctx, pathCond) =
  let (vars, typs) = L.unzip (mtd ^. Q.methodFormals)
      origThis = ctx ^. Q.ctxThis
      origScope = ctx ^. Q.ctxScope
      newScope = M.fromList (L.zip vars (L.zip args typs))
      ctx' = Lens.set Q.ctxThis addr (Lens.set Q.ctxScope newScope ctx)
   in do results <- symEval (mtd ^. Q.methodBody, ctx', pathCond)
         return $
           map
             (\(val, ctx'', pathCond') ->
                ( val
                , Lens.set
                    Q.ctxThis
                    origThis
                    (Lens.set Q.ctxScope origScope ctx'')
                , pathCond'))
             results

-- | Introduce path split for values that can be simplified further
-- with additional assumptions in the path condition:
force :: Result -> Verify Results
force (v@(Sym (Lookup k m)), ctx, pathCond)
  | TMap tk tv <- typeOfValue ctx m
  , valueHasType ctx k tk
  -- If we are trying to call a method on a symbolic map lookup, we split the
  -- path into a successful lookup and a failing one. If we have enough type
  -- information on the map, hopefully the call will be resolved to a type for
  -- which we know the method body.
   = do
    (fv, ctx', pathCond') <- typedValue "sym_lookup" tv ctx
    return
      [ (VInt 0, ctx, (v :=: VInt 0) : pathCond)
      , (fv, ctx', (v :=: fv) : Not (v :=: VInt 0) : pathCond' ++ pathCond)
      ]
force (v@(Sym (SymVar _ (TNamed t))), ctx, _)
  -- Allocate a new object of the required type
 = do
  (VRef a', ctx', pathCond') <- typedValue "sym_obj" (TNamed t) ctx
  return [(VRef a', ctx', v :=: VRef a' : pathCond')]
force (v, ctx, pathCond) = return [(v, ctx, pathCond)]

-- | Produce a list of symbolic values to use for method calls.
symArgs :: Context -> [(Var, Type)] -> Verify ([Value], Context, PathCond)
symArgs ctx args =
  Monad.foldM
    (\(vals, ctx', pathCond) (name, typ) -> do
       (val, ctx'', pathCond') <- typedValue name typ ctx'
       return (vals ++ [val], ctx'', pathCond' ++ pathCond) -- FIXME: vals ++ [val] is quadratic.  Also weird that path conditions are in reverse order from values.
     )
    ([], ctx, [])
    args

typedValue :: Var -> Type -> Context -> Verify Result
typedValue name (TTuple ts) ctx = do
  (vals, ctx', pathCond') <- symArgs ctx (L.zip (L.repeat name) ts)
  return (VTuple vals, ctx', pathCond')
typedValue _ (TNamed typ) ctx
  | Just tdecl <- ctx ^? Q.ctxTypeDecls . Lens.ix typ = do
    (args, ctx', pathCond') <-
      symArgs ctx (map (\(x, _, t) -> (x, t)) (tdecl ^. Q.typedeclFormals))
    (val, ctx'', pathCond'') <-
      Q.singleResult <$>
      symEval
        ( ENewConstr
            typ
            (L.zip
               (map (\(x, _, _) -> x) (tdecl ^. Q.typedeclFormals))
               (map EConst args))
        , ctx'
        , pathCond')
    let pathCondEqs =
          L.zipWith
            (\(x, _, _) argVal -> Sym (Deref val x) :=: argVal)
            (tdecl ^. Q.typedeclFormals)
            args
    return (val, ctx'', pathCondEqs ++ pathCond'')
  | otherwise = error $ "No such type: " ++ typ
typedValue name t ctx = do
  freshName <- freshVar name
  return (Sym (SymVar freshName t), ctx, [])

evalError :: String -> Context -> a
evalError s c = error (s ++ "\nContext:\n" ++ printContext c)
  where
    printLocal :: Var -> Local -> String
    printLocal name loc =
      "\t\t" ++ name ++ " = " ++ show (loc ^. Q.localValue) ++ " : " ++
      show (loc ^. Q.localType)
    printMethod :: Var -> Method -> String
    printMethod name mtd =
      L.unlines ["\t\t" ++ name ++ " { " ++ show (mtd ^. Q.methodBody) ++ " } "]
    printObject :: Addr -> Object -> String
    printObject addr obj =
      L.unlines $
      [ "  " ++ show addr ++ " |-> "
      , "\tAdversary?: " ++ show (obj ^. Q.objAdversary)
      , "\tLocals:"
      ] ++
      (map (uncurry printLocal) (M.toList (obj ^. Q.objLocals))) ++
      ["\tMethods:"] ++
      (map (uncurry printMethod) (M.toList (obj ^. Q.objMethods)))
    printContext :: Context -> String
    printContext ctx =
      L.unlines
        [ "this: " ++ show (ctx ^. Q.ctxThis)
        , "scope: " ++ show (ctx ^. Q.ctxScope)
        , "objects: " ++
          L.intercalate
            "\n"
            (map (uncurry printObject) (M.toList (ctx ^. Q.ctxObjs)))
        ]
