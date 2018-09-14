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
{-# LANGUAGE PatternSynonyms #-}
module Quivela.SymEval where

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

import Quivela.Language
import Quivela.Parse

-- | The fixed environment for symbolic evaluation. Currently this
-- only contains information about named types which are defined outside of quivela.
data VerifyEnv = VerifyEnv { _splitEq :: Bool
                           -- ^ Split == operator into two paths during symbolic evaluation?
                           , _useCache :: Bool
                           -- ^ Should we cache verification steps that succeed and not recheck them?
                           }
  deriving Typeable

-- | A monad for generating and discharging verification conditions, which
-- allows generating free variables and calling external solvers.
newtype Verify a = Verify { unVerify :: RWST VerifyEnv () VerifyState IO a }
  deriving ( Monad, MonadState VerifyState, MonadIO, Applicative, Functor
           , MonadReader VerifyEnv )
-- Right now, we only need the same environment as symbolic evaluation, so we reuse
-- that type here.

-- | Keeps track of fresh variables and, a z3 process, and which conditions
-- we already verified successfully in the past.
data VerifyState = VerifyState
  { _z3Proc :: (Handle, Handle, ProcessHandle)
    -- ^ For performance reasons, we spawn a Z3 process once and keep it around
  , _nextVar :: M.Map String Integer
  -- ^ Map of already used integers for fresh variable prefix
  , _alreadyVerified :: S.Set (Expr, Expr)
  -- ^ A cache of steps that we already verified before
  -- FIXME: Currently, we cannot serialize invariants, since they include functions as arguments
  -- in some cases
  }

-- Generate lenses for all types defined above:
concat <$> mapM makeLenses [ ''VerifyEnv, ''VerifyState ]

-- | Generate a fresh variable starting with a given prefix
freshVar :: String -> Verify String
freshVar prefix = do
  last <- use (nextVar . at prefix)
  case last of
    Just n -> do
      nextVar . ix prefix %= (+1)
      return $ "?" ++ prefix ++ show n
    Nothing -> do
      modify (nextVar . at prefix ?~ 0)
      freshVar prefix

type Config = (Expr, Context, PathCond)
type Result = (Value, Context, PathCond)
type Results = [Result]

-- | Throws an error if there is more than one result in the list. Used for
-- evaluating programs that are not supposed to have more than one result.
singleResult :: [Result] -> Result
singleResult [res@(_, _, _)] = res
singleResult ress = error $ "Multiple results: " ++ show ress


-- | Infer type of a symbolic value. Will return 'TAny' for most operations
-- except plain variables and inserting into a well-typed map.
typeOfSymValue :: Context -> SymValue -> Type
typeOfSymValue ctx (SymVar x t) = t
typeOfSymValue ctx (Proj tup idx) = TAny
-- we could have more precise type information here if the idx was constant
typeOfSymValue ctx (Insert key val map)
  | TMap tk tv <- typeOfValue ctx map =
  let tk' = if typeOfValue ctx key == tk then tk else TAny
      tv' = if typeOfValue ctx val == tv then tv else TAny
  in TMap tk' tv'
  | otherwise = TMap (typeOfValue ctx key) (typeOfValue ctx val)
  -- Insert always calls turns 'map' into an actual TMap
typeOfSymValue ctx (Lookup idx map) = TAny
  -- we don't know if idx is going to be in the map, so
  -- we can't give more precise type information here.
typeOfSymValue ctx (AdversaryCall _) = TAny
typeOfSymValue ctx (Add v1 v2)
  | typeOfValue ctx v1 == TInt && typeOfValue ctx v2 == TInt = TInt
  | otherwise = TAny
typeOfSymValue ctx (Ref a)
  -- If the reference points to an object, use that object's type of the reference
  -- I'm not sure if we shouldn't instead distinguish between a reference to a typed
  -- object and that typed object instead on the type level.
  | Just obj <- ctx ^. ctxObjs . at a = obj ^. objType
  | otherwise = TAny
typeOfSymValue ctx v = error $ "Not implemented: typeOfSymValue: " ++ show v

-- | Infer the type of a value. 'TAny' is returned when the inference can't
-- figure out anything more precise.
typeOfValue :: Context -> Value -> Type
typeOfValue ctx (VInt 0) = TAny
typeOfValue ctx (VInt i) = TInt
typeOfValue ctx VNil = TAny
typeOfValue ctx (Sym sv) = typeOfSymValue ctx sv
typeOfValue ctx (VTuple vs) = TTuple $ map (typeOfValue ctx) vs
typeOfValue ctx (VMap vs) = TMap tk tv
  where keyTypes = map (typeOfValue ctx) . M.keys $ vs
        valueTypes = map (typeOfValue ctx) . M.elems $ vs
        tk | [t] <- nub keyTypes = t -- all keys have same type
           | otherwise = TAny
        tv | [t] <- nub valueTypes = t
           | otherwise = TAny

-- | Monadic version of 'all'
allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM pred list = and <$> mapM pred list

-- | Check whether value has given type.
valueHasType :: Context -> Value -> Type -> Bool
valueHasType ctx _ TAny = True
valueHasType ctx (VInt 0) (TMap _ _) = True
valueHasType ctx (VInt i) TInt = True
valueHasType ctx (VTuple vs) (TTuple ts)
  | length vs == length ts = all (uncurry (valueHasType ctx)) (zip vs ts)
  | otherwise = False
valueHasType ctx (VMap values) (TMap tk tv) =
  all (\key -> valueHasType ctx key tk) (M.keys values) &&
  all (\val -> valueHasType ctx val tv) (M.elems values)
valueHasType ctx (Sym sv) t = symValueHasType ctx sv t
valueHasType _ _ _ = False

-- | Check if symbolic value has a given type.
symValueHasType :: Context -> SymValue -> Type -> Bool
symValueHasType ctx sv TAny = True
symValueHasType ctx (Add e1 e2) TInt = valueHasType ctx e1 TInt && valueHasType ctx e2 TInt
symValueHasType ctx (SymVar _ t') t = t == t'
symValueHasType ctx (Ref a) t
  | Just t' <- ctx ^? ctxObjs . ix a . objType = t == t'
symValueHasType ctx (Insert k v m) (TMap tk tv) = do
  -- TODO: this could be more precise: if we know that m is definitely not
  -- a map at this point, we can return True if k has type tk and v has type tv
  -- we should call the solver to check if this is the case to figure this out.
  and [ valueHasType ctx k tk
      , valueHasType ctx v tv
      , valueHasType ctx m (TMap tk tv)]
symValueHasType ctx _ _ = False

-- | Value to use to initialize new variables:
defaultValue :: Value
defaultValue = VInt 0

-- | Find the location of a variable in the context. Since this may have to add
-- a location for the variable in the scope or as a local, we also return an
-- updated context to use with the returned 'Place'. The 'Bool' component of the
-- result indicates if the context had to be modified.
findVar :: Var -> Context -> Maybe (Place, Context, Bool)
findVar x ctx
  | Just (v, t) <- M.lookup x (ctx ^. ctxScope) =
      Just $ (Place { _placeLens = ctxScope . ix x . _1
                    , _placeConst = False
                    , _placeType = t }, ctx, False)
  | Just loc <- ctx ^? ctxObjs . ix (ctx ^. ctxThis) . objLocals . ix x =
      Just $ (Place { _placeLens = ctxObjs . ix (ctx ^. ctxThis) . objLocals . ix x . localValue
                    , _placeConst = loc ^. localImmutable
                    , _placeType = loc ^. localType }, ctx, False)
  -- the variable doesn't exist yet, so we need to create it:
  -- if we're not in a global context, we use a local variable
  -- FIXME: this should probably check if we are inside a method instead, but currently
  -- we don't store whether this is the case in the context.
  | ctx ^. ctxThis /= 0 =
      Just $ (Place { _placeLens = ctxScope . ix x . _1
                    , _placeConst = False
                    , _placeType = TAny }
             , set (ctxScope . at x)
                   (Just (defaultValue, TAny)) ctx
             , True)
  | otherwise =
    Just $ ( Place { _placeLens = ctxObjs . ix 0 . objLocals . ix x . localValue
                   , _placeConst = False
                   , _placeType = TAny }
           , set (ctxObjs . ix 0 . objLocals . at x)
                 (Just (Local defaultValue TAny False)) ctx
           , True)

-- Define how to insert into a symbolic value via a lens:
type instance Index SymValue = Value
type instance IxValue SymValue = Value

instance Ixed SymValue where
  ix k f m = f (Sym $ Lookup k (Sym m)) <&> \v' -> Insert k v' (Sym m)

-- | Find or create the place of a valid l-value expression (i.e. a variable,
-- a projection, or an indexing expression with an l-value to the left of the [.
-- The result value has the same structure as the result of 'findVar', except
-- for an added path condition component.
findLValue :: Expr -> Context -> PathCond -> Verify [Maybe (Place, Context, PathCond, Bool)]
findLValue (EVar x) ctx pathCond =
  return [ fmap (\(place, ctx', created) -> (place, ctx', pathCond, created)) $ findVar x ctx]
findLValue (EProj obj name) ctx pathCond = do
  foreachM (symEval (obj, ctx, pathCond)) $ \case
    (VRef addr, ctx', pathCond')
      | Just loc <- ctx' ^? ctxObjs . ix addr . objLocals . ix name ->
          return [Just $ (Place { _placeLens = ctxObjs . ix addr . objLocals . ix name . localValue
                                , _placeConst = loc ^. localImmutable
                                , _placeType = loc ^. localType }, ctx', pathCond', False)]
    _ -> return [Nothing]
findLValue expr@(EIdx obj idx) ctx pathCond =
  foreachM (findLValue obj ctx pathCond) $ \case
    Nothing -> error $ "Invalid l-value: " ++ show expr
    Just (place, ctx', pathCond', created) ->
      foreachM (symEval (idx, ctx', pathCond')) $ \(idxVal, ctx'', pathCond'') ->
        case ctx'' ^? (place ^. placeLens) of
          Just (VMap m) ->
            case M.lookup idxVal m of
              Just _ -> return [Just ( Place { _placeLens = (place ^. placeLens) . valMap . ix idxVal
                                             , _placeType = TAny -- FIXME
                                             , _placeConst = False }
                                     , ctx'', pathCond'', False )]
              -- need to add the element to the map first to create a well-typed lens into it:
              -- this is because we use 'ix' instead of 'at' to access map elements, so the
              -- interface is the same as for lenses to an ordinary variable
              _ -> return [Just ( Place { _placeLens = (place ^. placeLens) . valMap . ix idxVal
                                        , _placeType = TAny -- FIXME
                                        , _placeConst = False }
                                , set ((place ^. placeLens) . valMap . at idxVal)
                                      (Just defaultValue)
                                      ctx''
                                , pathCond''
                                , True)]
          Just (Sym sv) -> return [Just ( Place { _placeLens = (place ^. placeLens) . symVal . ix idxVal
                                                , _placeType = TAny
                                                , _placeConst = False }
                                        , ctx''
                                        , pathCond''
                                        , False)]
          -- Not a map yet, create one:
          _ -> return [Just ( Place { _placeLens = (place ^. placeLens) . valMap . ix idxVal
                                    , _placeType = TAny -- FIXME
                                    , _placeConst = False }
                            , set (place ^. placeLens)
                                  (VMap $ M.fromList [(idxVal, defaultValue)])
                                  ctx''
                            , pathCond''
                            , True)]
findLValue expr ctx pathCond = error $ "invalid l-value: " ++ show expr


constAssignError :: a
constAssignError =  error "Assignment to constant variable"

illTypedAssignError :: Var -> Type -> Type -> a
illTypedAssignError x varType exprType =
  error $ "Ill-typed assignment to variable " ++ x ++ " of type " ++
          show varType ++ " of expression of type " ++ show exprType

-- Debugging functions for printing out a context in a nicer way.
-- | Turn a local into a human-readable string
printLocal :: Var -> Local -> String
printLocal name loc =
  "\t\t" ++ name ++ " = " ++ show (loc ^. localValue) ++ " : " ++ show (loc ^. localType)

-- | Turn a method into a human-readable string
printMethod :: Var -> Method -> String
printMethod name mtd = unlines
  ["\t\t" ++ name ++ " { " ++ show (mtd ^. methodBody) ++ " } "]

-- | Turn an object into a human-readable string
printObject :: Addr -> Object -> String
printObject addr obj = unlines $
  ["  " ++ show addr ++ " |-> "
  , "\tAdversary?: " ++ show (obj ^. objAdversary)
  ,"\tLocals:"] ++
  (map (uncurry printLocal) (M.toList (obj ^. objLocals))) ++
  ["\tMethods:"] ++
  (map (uncurry printMethod) (M.toList (obj ^. objMethods)))

-- | Turn a context into a human-readable string
printContext :: Context -> String
printContext ctx =
  unlines [ "this: " ++ show (ctx ^. ctxThis)
          , "scope: " ++ show (ctx ^. ctxScope)
          , "objects: " ++ intercalate "\n"
            (map (uncurry printObject) (M.toList (ctx ^. ctxObjs)))
          ]

evalError :: String -> Context -> a
evalError s ctx =
  error (s ++ "\nContext:\n" ++ printContext ctx)

lookupVar :: Var -> Context -> Value
lookupVar x ctx
  | Just (place, ctx', _) <- findVar x ctx, Just v <- ctx' ^? (place ^. placeLens) = v
  | otherwise = evalError ("No such variable: " ++ x) ctx

-- | Take a list of monadic actions producing lists and map another monadic function over
-- the list and concatenate all results. This is basically a monadic version of the
-- bind operator in the list monad.
foreachM :: (Monad m) => m [a] -> (a -> m [b]) -> m [b]
foreachM s act = do
  xs <- s
  ys <- mapM act xs
  return $ concat ys

-- | Add a method definition to the context
defineMethod :: Var -> [(Var, Type)] -> Expr -> MethodKind -> Context -> Context
defineMethod name formals body kind ctx
  | Just obj <- ctx ^? ctxObjs . at (ctx ^. ctxThis) =
      ctxObjs . ix (ctx ^. ctxThis) . objMethods . at name ?~
        (Method { _methodName = name
                , _methodFormals = formals
                , _methodBody = body
                , _methodKind = kind }) $ ctx
  | otherwise = error "failed to define method"

-- | Symbolically evaluate a list of field initializations in a given context and path condition
-- and return a list of possible executions of this list. Each element in the result is a list
-- of the same length where each field is evaluated, together with a context
symEvalFields :: [Field] -> Context -> PathCond -> Verify [([(Var, (Value, Type, Bool))], Context, PathCond)]
symEvalFields [] ctx pathCond = return [([], ctx, pathCond)]
symEvalFields (field : fields) ctx pathCond =
  foreachM (symEval (field ^. fieldInit, ctx, pathCond)) $ \(fieldVal, ctx', pathCond') -> do
    unless (valueHasType ctx' fieldVal (field ^. fieldType)) $ do
      error $ "Ill-typed argument for field initialization: " ++ show fieldVal ++
              " is not a subtype of " ++ show (field ^. fieldType)
    foreachM (symEvalFields fields ctx' pathCond') $ \(evaledFields, ctx'', pathCond'') ->
      return [((field ^. fieldName, (fieldVal, field ^. fieldType, field ^. immutable)) : evaledFields, ctx'', pathCond'')]

symEvalList :: [Expr] -> Context -> PathCond -> Verify [([Value], Context, PathCond)]
symEvalList [] ctx pathCond = return [([], ctx, pathCond)]
symEvalList (e : es) ctx pathCond =
  foreachM (symEval (e, ctx, pathCond)) $ \(val, ctx', pathCond') ->
    foreachM (symEvalList es ctx' pathCond') $ \(evaledList, ctx'', pathCond'') ->
      return [(val : evaledList, ctx'', pathCond'')]

-- | Return an unused address in the current context
nextAddr :: Context -> Addr
nextAddr ctx = case ctx ^. ctxAllocStrategy of
                 Increase -> maximum (M.keys (ctx ^. ctxObjs)) + 1
                 Decrease -> minimum (M.keys (ctx ^. ctxObjs)) - 1

-- | Uncurry a three-argument function (useful for partial application)
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

-- | Try to find a method of the given name in the object at that address
findMethod :: Addr -> Var -> Context -> Maybe Method
findMethod addr name ctx = ctx ^? ctxObjs . ix addr . objMethods . ix name

callMethod :: Addr -> Method -> [Value] -> Context -> PathCond -> Verify Results
callMethod addr mtd args ctx pathCond =
  let scope = M.fromList (zip (map fst (mtd ^. methodFormals))
                              (zip args (map snd (mtd ^. methodFormals))))
      ctx' = set ctxThis addr (set ctxScope scope ctx)
  in foreachM (symEval (mtd ^. methodBody, ctx', pathCond)) $ \(val, ctx'', pathCond') ->
       return [(val, set ctxThis (ctx ^. ctxThis) (set ctxScope (ctx ^. ctxScope) ctx''),
                pathCond')]

-- | Produce a list of symbolic values to use for method calls.
symArgs :: Context -> [(Var, Type)] -> Verify ([Value], Context, PathCond)
symArgs ctx args = foldM (\(vals, ctx', pathCond) (name, typ) -> do
                             (val, ctx'', pathCond') <- typedValue name typ ctx'
                             return (vals ++ [val], ctx'', pathCond' ++ pathCond)) ([], ctx, []) args
-- symArgs args = mapM (uncurry typedValue) args

typedValue :: Var -> Type -> Context -> Verify (Value, Context, PathCond)
typedValue name (TTuple ts) ctx = do
  (vals, ctx', pathCond') <- symArgs ctx (zip (repeat name) ts)
  return $ (VTuple vals, ctx', pathCond')
typedValue name (TNamed t) ctx
  | Just tdecl <- ctx ^? ctxTypeDecls . ix t = do
      (args, ctx', pathCond') <- symArgs ctx (map (\(name, immut, typ) -> (name, typ))
                                                  (tdecl ^. typedeclFormals))
      (val, ctx'', pathCond'') <- singleResult <$>
                          symEval (ENewConstr t (zip (map (\(name, _, _) -> name)
                                                          (tdecl ^. typedeclFormals))
                                                     (map EConst args)), ctx', pathCond')
      let pathCondEqs = zipWith (\(name, typ) argVal -> Sym (Deref val name) :=: argVal)
                                (map (\(name, immut, typ) -> (name, typ))
                                     (tdecl ^. typedeclFormals)) args
      return (val, ctx'', pathCondEqs ++ pathCond'')
  | otherwise = error $ "No such type: " ++ t
typedValue name t ctx = do
  freshName <- freshVar name
  return (Sym (SymVar freshName t), ctx, [])

-- | Introduce path split for values that can be simplified further
-- with additional assumptions in the path condition:
force :: Value -> Context -> PathCond -> Verify [Result]
force e@(Sym (Lookup k m)) ctx pathCond
  | TMap tk tv <- typeOfValue ctx m,
    valueHasType ctx k tk = do
  -- If we are trying to call a method on a symbolic map lookup, we split the
  -- path into a successful lookup and a failing one. If we have enough type
  -- information on the map, hopefully the call will be resolved to a type for
  -- which we know the method body.
  -- debug $ "Symbolic call on map lookup" ++ show (Lookup k m) ++ " of type: " ++ show (TMap tk tv)
  (fv, ctx', pathCond') <- typedValue "sym_lookup" tv ctx
  -- res <- symEval fv name args ctx' ((e :=: fv) : pathCond')
  return [ (VInt 0, ctx, (e :=: VInt 0) : pathCond)
         , (fv, ctx', (e :=: fv) : Not (e :=: VInt 0) : pathCond') ]
force (symVal@(Sym (SymVar sv (TNamed t)))) ctx pathCond = do
  -- Allocate a new object of the required type
  (VRef a', ctx', pathCond') <- typedValue "sym_obj" (TNamed t) ctx
  return [(VRef a', ctx', symVal :=: VRef a' : pathCond')]
force v ctx pathCond = return [(v, ctx, pathCond)]

-- | `symEvalCall obj name args ...` symbolically evaluates a method call to method name on object obj
symEvalCall :: Value -> Var -> [Value] -> Context -> PathCond -> Verify [(Value, Context, PathCond)]
symEvalCall (VRef addr) name args ctx pathCond
  | Just obj <- ctx ^. ctxObjs . at addr, obj ^. objAdversary =
      let newCalls = args : (ctx ^. ctxAdvCalls)
      in return [( Sym (AdversaryCall newCalls)
                 , set ctxAdvCalls newCalls ctx
                 , pathCond )]
  | Just mtd <- findMethod addr name ctx = callMethod addr mtd args ctx pathCond
  | otherwise = evalError ("Called non-existent method: " ++ name ++ "[" ++ show addr ++ "]") ctx
symEvalCall VNil "Z" [m] ctx pathCond = return [(Sym (Z m), ctx, pathCond)]
symEvalCall VNil "rnd" [] ctx pathCond = symEval (ENew [] ENop, ctx, pathCond)
symEvalCall VNil "+" [arg1, arg2] ctx pathCond
  | isSymbolic arg1 || isSymbolic arg2 =
      return [(Sym (Add arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1, VInt m <- arg2 =
      return [(VInt (n + m), ctx, pathCond)]
  | otherwise  = error $ "Addition of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "-" [arg1, arg2] ctx pathCond
  | isSymbolic arg1 || isSymbolic arg2 =
      return [(Sym (Sub arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1, VInt m <- arg2 =
      return [(VInt (n - m), ctx, pathCond)]
  | otherwise = error $ "Subtraction of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "*" [arg1, arg2] ctx pathCond
  | isSymbolic arg1 || isSymbolic arg2 =
      return [(Sym (Mul arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1, VInt m <- arg2 =
      return [(VInt (n * m), ctx, pathCond)]
  | otherwise = error $ "Multiplication of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "/" [arg1, arg2] ctx pathCond
  | isSymbolic arg1 || isSymbolic arg2 =
      return [(Sym (Div arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1, VInt m <- arg2 =
      if m == 0 then return [((VInt 0), ctx, pathCond)]
      else return [(VInt (n `div` m), ctx, pathCond)]
  | otherwise = error $ "Division of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "<" [arg1, arg2] ctx pathCond
  | isSymbolic arg1 || isSymbolic arg2 =
      return [(Sym (Lt arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1, VInt m <- arg2 =
      return [(if n < m then VInt 1 else VInt 0, ctx, pathCond)]
  | otherwise = error $ "Comparison of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil "<=" [arg1, arg2] ctx pathCond
  | isSymbolic arg1 || isSymbolic arg2 = return [(Sym (Le arg1 arg2), ctx, pathCond)]
  | VInt n <- arg1, VInt m <- arg2 =
      return [(if n <= m then VInt 1 else VInt 0, ctx, pathCond)]
  | otherwise = error $ "Comparison of non-symbolic non-integers: " ++ show (arg1, arg2)
symEvalCall VNil name args ctx pathCond
  | Just mtd <- findMethod (ctx ^. ctxThis) name ctx =
      callMethod (ctx ^. ctxThis) mtd args ctx pathCond
  | Just mtd <- findMethod 0 name ctx =
      callMethod 0 mtd args ctx pathCond
  | otherwise = error $ "Call to non-existent method: " ++ name
symEvalCall (Sym sv) name args ctx pathCond = do
  forced <- force (Sym sv) ctx pathCond
  if forced == [(Sym sv, ctx, pathCond)]
     then do
       debug $ "Not implemented: calls on untyped symbolic objects: (" ++
               show sv ++ ")." ++ name ++ "(" ++ show args ++ ")"
       -- we return a fresh variable here to encode that we have no information
       -- about the returned value; FIXME: we should also havoc everything
       -- the base object may have access to.
       -- This case can still yield a provable verification condition
       -- if the path condition is contradictory
       fv <- freshVar "untyped_symcall"
       return [(Sym (SymVar fv TAny), ctx, pathCond)]
     else foreachM (return forced) $ \(val, ctx', pathCond') -> do
       -- debug $ "Forced symbolic value to: " ++ show (val, ctx', pathCond')
       symEvalCall val name args ctx' pathCond'
symEvalCall (VInt 0) name args ctx pathCond = return [((VInt 0), ctx, pathCond)]
symEvalCall obj name args ctx pathCond =
  error $ "Bad method call[" ++ show obj ++ "]: " ++ name ++ "\n" ++ show ctx

lookupInTuple :: Value -> Value -> Value
lookupInTuple (VTuple vs) (VInt i)
  | fromInteger i < length vs = vs !! fromInteger i
  | otherwise = error "Invalid tuple index"
lookupInTuple tup (Sym sidx) = Sym (Proj tup (Sym sidx))
lookupInTuple (Sym sv) vidx = Sym (Proj (Sym sv) vidx)
lookupInTuple _ _ = error "invalid tuple lookup"

isSymbolic :: Value -> Bool
isSymbolic (Sym _) = True
isSymbolic _ = False

-- | Returns the name of the variable for variable expressions, and @Nothing@ if not.
fromEVar :: Expr -> Maybe String
fromEVar (EVar x) = Just x
fromEVar _ = Nothing

-- | Evaluate a pattern-match expression with list of variables on LHS and another expression
-- on the right-hand side. This corresponds to writing @<x1, .., xn> = rhs@. Currently,
-- this does not support nested patterns.
symEvalPatternMatch :: [Expr] -> Expr -> Context -> PathCond -> Verify Results
symEvalPatternMatch pat rhs ctx pathCond
  -- check that all elements of the pattern are just simple variables
  | [vars] <- sequence (map (maybeToList . fromEVar) pat) =
  foreachM (symEval (rhs, ctx, pathCond)) $ \(vrhs, ctx', pathCond') ->
    let (lvalues, ctx', isNew) =
          foldr (\var (places, ctx', isNew) ->
                    case findVar var ctx' of
                      Just (place, ctx'', isNew') -> (place : places , ctx'', isNew || isNew')
                      Nothing -> error $ "Not a valid l-value: " ++ show var) ([], ctx, False) vars
        rhsVals = if isSymbolic vrhs
                  then map (Sym . Proj vrhs . VInt . fromIntegral) [0..length pat - 1]
                  else case vrhs of
                        VTuple rhsVals | length rhsVals == length vars -> rhsVals
                        _ -> error $ "Invalid concrete value for pattern-match expression: " ++ show (pat, rhs)
        ctx''' = foldr (\(place, proj) ctx'' -> set (place ^. placeLens) proj ctx'') ctx' (zip lvalues rhsVals)
        projEq = if isSymbolic vrhs then [vrhs :=: VTuple rhsVals] else []
    in return [(vrhs, ctx''', projEq ++ pathCond)]
  | otherwise = error $ "Nested patterns not supported yet: " ++ show pat ++ " = " ++ show rhs

symEval :: Config -> Verify Results
symEval (ENop, ctx, pathCond) = return [(VNil, ctx, pathCond)]
symEval (EConst v, ctx, pathCond) = return [(v, ctx, pathCond)]
symEval (EVar x, ctx, pathCond) = return [(lookupVar x ctx, ctx, pathCond)]
symEval (ETuple es, ctx, pathCond) =
  foreachM (symEvalList es ctx pathCond) $ \(vs, ctx', pathCond') ->
    return [(VTuple vs, ctx', pathCond')]
symEval (ETupleProj etup eidx, ctx, pathCond) =
  foreachM (symEval (etup, ctx, pathCond)) $ \(vtup, ctx', pathCond') ->
    foreachM (symEval (eidx, ctx', pathCond')) $ \(vidx, ctx'', pathCond'') ->
      return [(lookupInTuple vtup vidx, ctx'', pathCond'')]
symEval (expr@(EProj obj name), ctx, pathCond) =
  foreachM (symEval (obj, ctx, pathCond)) $ \(val, ctx', pathCond') ->
    case val of
      VRef addr
        | Just loc <- ctx' ^? ctxObjs . ix addr . objLocals . ix name ->
          return [(loc ^. localValue, ctx', pathCond')]
      Sym sv -> do
        -- we might be able to make progress from here by forcing
        -- the receiver value to something more concrete:
        forced <- force (Sym sv) ctx pathCond
        if forced == [(val, ctx', pathCond')]
        then return [(Sym (Deref val name), ctx', pathCond')]
        else foreachM (pure forced) $ \(val', ctx'', pathCond'') -> do
          symEval (EProj (EConst val') name, ctx'', pathCond'')
      -- VInt 0 -> return [(VInt 0, ctx', pathCond')]
      _ -> return [(Sym (Deref val name), ctx', pathCond')]
symEval (EIdx base idx, ctx, pathCond) =
  foreachM (symEval (base, ctx, pathCond)) $ \(baseVal, ctx', pathCond') ->
    foreachM (symEval (idx, ctx', pathCond')) $ \(idxVal, ctx'', pathCond'') ->
      case baseVal of
        VInt 0 -> return [(VInt 0, ctx'', pathCond'')] -- 0 is the empty map
        VMap vals -> if isSymbolic idxVal
                     then return [(Sym (Lookup idxVal baseVal), ctx'', pathCond'')]
                     else case M.lookup idxVal vals of
                       Just val -> return [(val, ctx'', pathCond'')]
                       Nothing -> if isSymbolic idxVal
                                  -- if we can't find the value in the map, keep the lookup symbolic:
                                  then return [(Sym (Lookup idxVal baseVal), ctx'', pathCond'')]
                                  else return [((VInt 0), ctx'', pathCond'')]
        Sym sv -> return [(Sym (Lookup idxVal baseVal), ctx'', pathCond'')]
        _ -> return [((VInt 0), ctx'', pathCond'')]
symEval (EAssign (ETuple pat) rhs, ctx, pathCond) = symEvalPatternMatch pat rhs ctx pathCond
symEval (EAssign lhs rhs, ctx, pathCond) =
  foreachM (symEval (rhs, ctx, pathCond)) $ \(rhsVal, ctx', pathCond') ->
    foreachM (findLValue lhs ctx' pathCond') $ \case
      Just (place, ctx'', pathCond'', created) -> do
        unless (valueHasType ctx'' rhsVal (place ^. placeType)) $ do
          error $ "Ill-typed assignment from value of type: " ++ show (typeOfValue ctx'' rhsVal) ++
                   " to place with type: " ++ show (place ^. placeType)
        when (place ^. placeConst) $ do
          error $ "Assignment to constant location: " ++ show lhs
        return [(rhsVal, set (place ^. placeLens) rhsVal ctx'', pathCond'')]
      _ -> error $ "Invalid l-value: " ++ show lhs
symEval (EIf cnd thn els, ctx, pathCond) = do
  foreachM (symEval (cnd, ctx, pathCond)) handle
  where handle (cndVal, ctx', pathCond')
          | isSymbolic cndVal = do
              thnPaths <- symEval (thn, ctx', Not (cndVal :=: (VInt 0)) : pathCond')
              elsPaths <- symEval (els, ctx', cndVal :=: (VInt 0) : pathCond')
              return $ thnPaths ++ elsPaths
          | cndVal == VInt 0 = symEval (els, ctx', pathCond')
          | otherwise = symEval (thn, ctx', pathCond')
symEval (ESeq e1 e2, ctx, pathCond) = do
  foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    symEval (e2, ctx', pathCond')
symEval (EMethod name formals body mtdKind, ctx, pathCond) = do
  return [(VNil, defineMethod name formals body mtdKind ctx, pathCond)]
symEval (ECall (EConst VNil) "++" [lval], ctx, pathCond) = do
  foreachM (findLValue lval ctx pathCond) $ \case
    Just (place, ctx', pathCond', False)
      | Just oldVal <- ctx' ^? (place ^. placeLens) -> do
      updPaths <- symEval ( EAssign lval (ECall (EConst VNil) "+" [lval, EConst (VInt 1)])
                          , ctx', pathCond')
      return . map (\(newVal, ctx'', pathCond'') -> (oldVal, ctx'', pathCond'')) $ updPaths
    _ -> error $ "Invalid l-value in post-increment: " ++ show lval
symEval (ECall (EConst VNil) "==" [e1, e2], ctx, pathCond) =
  foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    foreachM (symEval (e2, ctx', pathCond')) $ \(v2, ctx'', pathCond'') -> do
      doSplit <- view splitEq
      if (isSymbolic v1 || isSymbolic v2) && (v1 /= v2)
      then if doSplit
           then return [ (VInt 0, ctx'', Not (v1 :=: v2) : pathCond'')
                       , (VInt 1, ctx'', v1 :=: v2 : pathCond'')]
           else return [(Sym (ITE (v1 :=: v2) (VInt 1) (VInt 0)), ctx'', pathCond'')]
      else if v1 == v2
           then return [ (VInt 1, ctx'', pathCond'') ]
           else return [ (VInt 0, ctx'', pathCond'') ]
symEval (ECall (EConst VNil) "!" [e], ctx, pathCond) = do
  foreachM (symEval (e, ctx, pathCond)) $ \(v, ctx', pathCond') ->
    case v of
      Sym sv -> return [ (VInt 1, ctx', v :=: VInt 0 : pathCond')
                       , (VInt 0, ctx', Not (v :=: (VInt 0)) : pathCond') ]
      (VInt 0) -> return [ (VInt 1, ctx', pathCond') ]
      _ -> return [ ((VInt 0), ctx', pathCond') ]
symEval (ECall (EConst VNil) "&" [e1, e2], ctx, pathCond) = do
  foreachM (symEval (e1, ctx, pathCond)) handleCase
  where
    handleCase ((VInt 0), ctx', pathCond') = return [((VInt 0), ctx', pathCond')]
    handleCase (Sym sv, ctx', pathCond') = do
      -- TODO: ask verifier if v can be proven to be Error/not-Error
      cfgs <- symEval (e2, ctx', Not (Sym sv :=: VInt 0) : pathCond')
      return $ ((VInt 0), ctx', Sym sv :=: VInt 0 : pathCond') : cfgs
    handleCase (v, ctx', pathCond') = symEval (e2, ctx', pathCond')
symEval (ECall (EConst VNil) "|" [e1, e2], ctx, pathCond) = do
  foreachM (symEval (e1, ctx, pathCond)) handleCase
  where
    handleCase ((VInt 0), ctx', pathCond') = symEval (e2, ctx', pathCond')
    handleCase (Sym sv, ctx', pathCond') = do
      cfgs <- symEval (e2, ctx', (Sym sv :=: VInt 0) : pathCond')
      return $ (Sym sv, ctx', Not (Sym sv :=: VInt 0) : pathCond') : cfgs
    handleCase (v, ctx', pathCond') = return [(v, ctx', pathCond')]
symEval (ECall (EConst VNil) "adversary" [], ctx, pathCond) = do
  return [(VRef (nextAddr ctx)
          , ctxObjs . at (nextAddr ctx) ?~
            (Object { _objLocals = M.empty, _objMethods = M.empty
                    , _objType = TAny
                    , _objAdversary = True }) $ ctx
          , pathCond)]
symEval (ECall obj name args, ctx, pathCond) =
  foreachM (symEval (obj, ctx, pathCond)) $ \(vobj, ctx', pathCond') ->
   foreachM (symEvalList args ctx' pathCond') $ \(evaledArgs, ctx'', pathCond'') ->
     symEvalCall vobj name evaledArgs ctx'' pathCond''
symEval (ENew fields body, ctx, pathCond) =
  foreachM (symEvalFields fields ctx pathCond) $ \(evaledFields, ctx', pathCond') ->
    let locals = M.fromList (map (second (uncurry3 Local)) evaledFields)
        ctx'' = ctxObjs . at (nextAddr ctx') ?~ Object { _objLocals = locals
                                                       , _objMethods = M.empty
                                                       , _objType = TAny
                                                       , _objAdversary = False
                                                       } $ ctx'
        ctx''' = set ctxThis (nextAddr ctx') ctx''
    in foreachM (symEval (body, ctx''', pathCond')) $ \(bodyVal, ctx'''', pathCond'') ->
      return [(VRef (nextAddr ctx'), set ctxThis (ctx' ^. ctxThis) ctx'''', pathCond'')]
symEval (tdecl@(ETypeDecl name formals values body), ctx, pathCond)
  | name `elem` M.keys (ctx ^. ctxTypeDecls) =
    error $ "Duplicate type declaration: " ++ name
  | otherwise = return [(VNil, ctxTypeDecls . at name ?~ tdecl $ ctx, pathCond)]
symEval (expr@(ENewConstr typeName args), ctx, pathCond)
  | Just tdecl <- ctx ^. ctxTypeDecls . at typeName = do
      -- evaluate new expression stored for the type, then set the object's type
      -- to keep track that this was constructed with a constructor
      unless (map fst args == map (\(name, _, _) -> name) (tdecl ^. typedeclFormals)) $
        (error $ "Mismatch between actual and expected constructor arguments: " ++ show expr)
      let fields = zipWith (\(name, expr) (_, immut, typ) ->
                              Field { _fieldName = name
                                    , _fieldInit = expr
                                    , _immutable = immut
                                    , _fieldType = typ }) args (tdecl ^. typedeclFormals) ++
                   map (\(name, val) -> Field { _fieldName = name
                                              , _fieldInit = expr
                                              , _immutable = False -- FIXME
                                              , _fieldType = typeOfValue ctx val }) (tdecl ^. typedeclValues)

      foreachM (symEval (ENew fields (fromJust $ tdecl ^? typedeclBody), ctx, pathCond)) $ \(val, ctx', pathCond') ->
        case val of
          VRef addr ->
            return [(val, ctxObjs . ix addr . objType .~ TNamed typeName $ ctx', pathCond')]
          _ -> return [(val, ctx', pathCond')] -- object creation may have returned an error
  | otherwise = error $ "No such type: " ++ typeName
symEval (setCompr@ESetCompr{}, ctx, pathCond) = do
  let x = setCompr ^. comprVar
  -- Get new symbolic variable for variable bound by comprehension:
  fv <- (Sym . (`SymVar` TAny)) <$> freshVar x
  -- Bind name in new context, in which we can evaluate predicate
  -- and function expression of comprehension
  let newCtx = over ctxScope (M.insert x (fv, TAny)) ctx
  predPaths <- symEval (fromJust (setCompr ^? comprPred), newCtx, pathCond)
  comprs <- foreachM (pure predPaths) $ \(predVal, ctx', pathCond') ->
    -- foreachM (symEval (fromJust (setCompr ^? comprBase)
    foreachM (symEval (fromJust (setCompr ^? comprValue), ctx', pathCond')) $ \(funVal, ctx'', pathCond'') -> do
      return [Sym (SetCompr funVal x (conjunction $ Not (predVal :=: VInt 0) : pathCond''))]
  return [(foldr (\sc v -> Sym (Union sc v)) (VSet S.empty) comprs, ctx, pathCond)]
symEval (mapCompr@EMapCompr{}, ctx, pathCond) = do
  let x = mapCompr ^. comprVar
  -- FIXME: factor out commonalities with ESetCompr case
  fv <- freshVar x
  let fvExpr = Sym (SymVar fv TAny)
  let newCtx = over ctxScope (M.insert x (fvExpr, TAny)) ctx
  predPaths <- symEval (fromJust (mapCompr ^? comprPred), newCtx, pathCond)
  comprs <- foreachM (pure predPaths) $ \(predVal, ctx', pathCond') ->
    foreachM (symEval (fromJust (mapCompr ^? comprValue), newCtx, pathCond)) $ \(funVal, ctx'', pathCond'') -> do
      return [Sym (MapCompr fv funVal (conjunction $ Not (predVal :=: VInt 0) : pathCond' ++ pathCond''))]
  return [(foldr (\sc v -> Sym (MapUnion sc v)) (VMap M.empty) comprs, ctx, pathCond)]
symEval (EIn elt set, ctx, pathCond) = do
  foreachM (symEval (elt, ctx, pathCond)) $ \(velt, ctx', pathCond') ->
    foreachM (symEval (set, ctx', pathCond'))  $ \(vset, ctx'', pathCond'') -> do
      if (isSymbolic velt || isSymbolic vset)
      then return [(Sym (In velt vset), ctx'', pathCond'')]
      else case vset of
             VSet vals -> (if velt `S.member` vals then return [(VInt 1, ctx'', pathCond'')]
                           else return [(VInt 0, ctx'', pathCond'')])
             _ -> error $ "Tried to test for set membership in concrete non-set value: " ++ show vset
symEval (ESubmap e1 e2, ctx, pathCond) = do
  foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    foreachM (symEval (e2, ctx', pathCond')) $ \(v2, ctx'', pathCond'') -> do
      if isSymbolic v1 || isSymbolic v2
      then return [(Sym (Submap v1 v2), ctx'', pathCond'')]
      else case (v1, v2) of
             (VMap m1, VMap m2) -> if (S.fromList (M.keys m1) `S.isSubsetOf` S.fromList (M.keys m2))
                                   then return [(VInt 1, ctx'', pathCond'')]
                                   else return [(VInt 0, ctx'', pathCond'')]
             _ -> error $ "Concrete non-map arguments for ⊆ operator: " ++ show (v1, v2)
symEval (EAssume e1 e2, ctx, pathCond) =
  return [(VNil, over ctxAssumptions ((e1, e2):) ctx, pathCond)]
-- symEval (e, ctx, pathCond) = error $ "unhandled case" ++ show e

emptyVerifyEnv :: VerifyEnv
emptyVerifyEnv = VerifyEnv { _splitEq = False, _useCache = True }

conjunction :: [Prop] -> Prop
conjunction [] = PTrue
conjunction [p] = p
conjunction ps = foldr1 (:&:) ps
