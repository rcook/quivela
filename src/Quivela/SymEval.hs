{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
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
type Scope = M.Map Var Value
type Env = M.Map Var Value
data Type = TInt | TTuple [Type] | TMap Type Type | TAny
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | Symbolic values representing unknowns and operations on the
-- Calls to the adversary are also symbolic.
data SymValue = SymVar String Type
  | Insert Value Value Value
  | Proj Value Value
  | Lookup Value Value
  | AdversaryCall [[Value]]
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

-- | Quivela values
data Value = VInt Integer
  | VMap { _valMap :: M.Map Value Value }
  | VTuple [Value]
  | VError
  | VNil
  | VRef Addr
  | Sym SymValue
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)
makeLenses ''Value

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
          | ENew { _newFields :: [Field]
                 , _newBody :: Expr }
          | EMethod { _emethodName :: String
                    , _emethodArgs :: [(String, Type)]
                    , _emethodBody :: Expr }
          | ECall { _callObj :: Expr
                  , _callName :: String
                  , _callArgs :: [Expr] }
          | ECVar Expr Var Expr
          | ETuple [Expr]
          | ETupleProj Expr Expr
          | ESeq Expr Expr
  deriving (Eq, Read, Show, Ord, Data, Typeable, Generic)

instance Serialize SymValue
instance Serialize Value
instance Serialize Type
instance Serialize Field
instance Serialize Expr

-- instance Hashable SymValue
-- instance Hashable Value
-- instance Hashable Type
-- instance Hashable Field
-- instance Hashable Expr

makeLenses ''Field
makeLenses ''Expr

-- | The value of a field of an object in the heap
data Local = Local { _localValue :: Value
                   , _localType :: Type
                   , _localImmutable :: Bool }
  deriving (Eq, Read, Show, Ord, Data, Typeable)

makeLenses ''Local

data Method = Method { _methodName :: String
                     , _methodFormals :: [(String, Type)]
                     , _methodBody :: Expr
                     }
  deriving (Eq, Read, Show, Ord, Data, Typeable)
makeLenses ''Method

data Object = Object { _objLocals :: M.Map Var Local
                     , _objMethods :: M.Map Var Method
                     , _objAdversary :: Bool -- ^ Is the object an adversary?
                     }
  deriving (Eq, Read, Show, Ord, Data, Typeable)
makeLenses ''Object

data Context = Context { _ctxObjs :: M.Map Addr Object
                       , _ctxThis :: Addr
                       , _ctxScope :: Scope -- ^ Keeps track of local variables and arguments in a
                                            -- method call.
                       , _ctxAdvCalls :: [[Value]] -- ^ All adversary calls so far
                       }
  deriving (Eq, Read, Show, Ord, Data, Typeable)

makeLenses ''Context

-- | We don't need any state (other than contexts and path conditions with are passed explicitly)
-- but we might need in the future, so we leave this stub here.
data SymEvalState = SymEvalState { }
makeLenses ''SymEvalState

-- | A monad for symbolic evaluation. Right now this is unnecessary, but at least
-- the IO part is probably going to become necessary in the future for solver calls
-- to rule out some paths that we don't need to explore.
newtype SymEval a = SymEval { unSymEval :: RWST () () SymEvalState IO a }
  deriving (Monad, Applicative, Functor)

-- | Propositions. These are used both to keep track of the path condition
-- as well as for the verification conditions we generate later on.
data Prop = Value :=: Value
  | Not Prop
  | Forall [(Var, Type)] Prop
  | Prop :=>: Prop
  | Prop :&: Prop
  | PTrue | PFalse
  deriving (Eq, Read, Show, Ord, Data, Typeable)

-- | A path condition is a list of propositions that all hold on a given path
-- These could be stored as just one big conjunction instead, but representing
-- them as a list simplifies reasoning about which paths are prefixes of others.
type PathCond = [Prop]

type Config = (Expr, Context, PathCond)
type Result = (Value, Context, PathCond)
type Results = [Result]

-- | Subtyping relation. @t <: s@ holds iff t is a subtype of s.
(<:) :: Type -> Type -> Bool
x <: TAny = True
TMap tk tv <: TMap tk' tv' = tk <: tk' && tv <: tv'
TTuple ts <: TTuple ts' = length ts == length ts' && and (zipWith (<:) ts ts')
TInt <: TInt = True
_ <: _ = False

-- | Infer type of a symbolic value. Will return 'TAny' for most operations
-- except plain variables and inserting into a well-typed map.
typeOfSymValue :: SymValue -> Type
typeOfSymValue (SymVar x t) = t
typeOfSymValue (Proj tup idx) = TAny
-- we could have more precise type information here if the idx was constant
typeOfSymValue (Insert key val map)
  | TMap tk tv <- typeOfValue map =
  let tk' = if typeOfValue key == tk then tk else TAny
      tv' = if typeOfValue val == tv then tv else TAny
  in TMap tk' tv'
  | otherwise = TMap (typeOfValue key) (typeOfValue val)
  -- Insert always calls turns 'map' into an actual TMap
typeOfSymValue (Lookup idx map) = TAny
  -- we don't know if idx is going to be in the map, so
  -- we can't give more precise type information here.

typeOfSymValue (AdversaryCall _) = TAny

-- | Infer the type of a value. 'TAny' is returned when the inference can't
-- figure out anything more precise.
typeOfValue :: Value -> Type
typeOfValue (VInt i) = TInt
typeOfValue VError = TAny
typeOfValue VNil = TAny
typeOfValue (VRef a) = TAny
typeOfValue (Sym sv) = typeOfSymValue sv
typeOfValue (VTuple vs) = TTuple $ map typeOfValue vs
typeOfValue (VMap vs) = TMap tk tv
  where keyTypes = map typeOfValue . M.keys $ vs
        valueTypes = map typeOfValue . M.elems $ vs
        tk | [t] <- nub keyTypes = t -- all keys have same type
           | otherwise = TAny
        tv | [t] <- nub valueTypes = t
           | otherwise = TAny

-- | Return a lens to a given variable in the context:
-- If the variable is in the current scope, return that;
-- If the variable is a local of the current object, return that
-- Otherwise try looking up the variable in the global object.
-- If findVar x ctx = Just (lens, isConst, t), then the variable
-- can be accessed via lens, isConst is True iff the variable is
-- mutable and t is the variable's type.
-- @findVar :: Var -> Context -> (Lens' Context Value, Bool, Type)@
findVar x ctx
  | Just v <- M.lookup x (ctx ^. ctxScope) =
      Just (ctxScope . ix x, False, TAny) -- Local variables don't have types at the moment
  | otherwise =
    case ctx ^? lens of
      Just loc -> Just ( ctxObjs . ix (ctx ^. ctxThis) . objLocals . ix x . localValue
                       , loc ^. localImmutable
                       , loc ^. localType)
      _ -> Nothing
  where lens = ctxObjs . ix (ctx ^. ctxThis) . objLocals . ix x

constAssignError :: a
constAssignError =  error "Assignment to constant variable"

illTypedAssignError :: Var -> Type -> Type -> a
illTypedAssignError x varType exprType =
  error $ "Ill-typed assignment to variable " ++ x ++ " of type " ++
          show varType ++ " of expression of type " ++ show exprType

-- | Update the value of a variable. If the variable already exists,
-- just use the lens from `findVar` to set it. Otherwise add it
-- to the current scope if we are in a non-global method call, and
-- add it as a global otherwise
updateVar :: Var -> Value -> Context -> Context
updateVar x val ctx
  | Just (lens, isConst, t) <- findVar x ctx =
    if isConst then constAssignError
    else if typeOfValue val <: t then set lens val ctx
         else illTypedAssignError x t (typeOfValue val)
  | ctx ^. ctxThis > 0 = (ctxScope . at x) ?~ val $ ctx
  | otherwise =
      ctxObjs . ix 0 . objLocals . at x ?~ (Local val TAny False) $ ctx


-- | Return a lens to the given object field.
-- findIdxVar :: Addr -> Var -> Value -> Context -> Maybe (Lens' Context Value, Context)
findObjVar addr name ctx
  | Just loc <- ctx ^? ctxObjs . ix addr . objLocals . ix name =
      -- construction of the lens is duplicated here due to GHC getting confused
      -- about the polymorphic types involved.
      Just ( ctxObjs . ix addr . objLocals . ix name . localValue
           , loc ^. localImmutable
           , loc ^. localType)
  | otherwise = Nothing


updateECVar :: Value -> Var -> Value -> Value -> Context -> Context
updateECVar (VRef a) name idx newValue ctx
  | Just (lens, isConst, varType) <- findObjVar a name ctx,
    valueType <- typeOfValue newValue =
      if isConst then constAssignError else
      if not (valueType <: varType)
      then illTypedAssignError name varType valueType
      else
      case idx of
        VNil -> set lens newValue ctx
        _ -> let Just (lens', _, _) = findObjVar a name ctx
             in case ctx ^? lens' of
                  Just (VMap vs) -> lens . valMap . at idx ?~ newValue $ ctx
                  Just (Sym sv) -> set lens (Sym (Insert idx newValue (Sym sv))) ctx
                  Just _ -> set lens (VMap (M.singleton idx newValue)) ctx
updateECVar VNil name VNil newValue ctx = updateVar name newValue ctx
updateECVar VNil name idx newValue ctx
  | Just (lens, isConst, varType) <- findObjVar (ctx ^. ctxThis) name ctx,
    Just (lens', _, _) <- findObjVar (ctx ^. ctxThis) name ctx,
    Just v <- ctx ^? lens', valueType <- typeOfValue newValue =
      if isConst then constAssignError else
      if not (valueType <: varType)
      then illTypedAssignError name varType valueType
      else case v of
             VMap vs -> lens . valMap . at idx ?~ newValue $ ctx
             Sym sv -> set lens (Sym (Insert idx newValue (Sym sv))) ctx
             _ -> set lens (VMap (M.singleton idx newValue)) ctx
updateECVar VNil name idx newValue ctx =
  error $ "Unhandled case VNil." ++ name ++ "." ++ show idx ++ " |-> " ++ show newValue

-- | Look up a possibly nil index in a field. If the index is nil, this
-- simply retrieves the given value (e.g. in expressions like obj.f)
-- If idx is non-nil, the value must either be a concrete map, or
-- a symbolic value, in which case we either retrieve the value directly
-- or return a symbolic expression representing the lookup
lookupIndex :: Value -> Value -> [(Value, PathCond)]
lookupIndex baseMap VNil = [(baseMap, [])]
lookupIndex (VMap vals) idx
  | Just v <- M.lookup idx vals = [(v, [])]
  | otherwise = [(VError, [])]
lookupIndex (Sym sv) idx = [(Sym (Lookup idx (Sym sv)), [])]
lookupIndex _ idx = [(VError, [])]

-- | Look up a variable access of the for obj.name[idx], where both
-- obj or idx can be nil.
lookupECVar (VRef a) name idx ctx
  | Just (lens, isConst, varType) <- findObjVar a name ctx,
    Just v <- ctx ^? lens = fst . head $ lookupIndex v idx
  | otherwise = error "Lookup on non-existent object"
lookupECVar (VTuple vs) name (VInt i) ctx
  | fromInteger i < length vs = vs !! fromInteger i
  | otherwise = error "Invalid tuple lookup"
lookupECVar VNil name idx ctx
  | Just (lens, isConst, varType) <- findObjVar (ctx ^. ctxThis) name ctx,
    Just v <- ctx ^? lens = fst . head $ lookupIndex v idx
  | Just (lens, isConst, varType) <- findObjVar 0 name ctx,
    Just v <- ctx ^? lens = fst . head $ lookupIndex v idx


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
  | Just (lens, _, _) <- findVar x ctx, Just v <- ctx ^? lens = v
  | otherwise = evalError ("No such variable: " ++ x) ctx

-- | Take a list of monadic actions producing lists and map another monadic function over
-- the list and concatenate all results. This is basically a monadic version of the
-- bind operator in the list monad.
foreachM :: (Ord b, Monad m) => m [a] -> (a -> m [b]) -> m [b]
foreachM s act = do
  xs <- s
  ys <- mapM act xs
  return $ concat ys

-- | Add a method definition to the context
defineMethod :: Var -> [(Var, Type)] -> Expr -> Context -> Context
defineMethod name formals body ctx
  | Just obj <- ctx ^? ctxObjs . at (ctx ^. ctxThis) =
      ctxObjs . ix (ctx ^. ctxThis) . objMethods . at name ?~
        (Method name formals body) $ ctx
  | otherwise = error "failed to define method"

-- | Symbolically evaluate a list of field initializations in a given context and path condition
-- and return a list of possible executions of this list. Each element in the result is a list
-- of the same length where each field is evaluated, together with a context
symEvalFields :: [Field] -> Context -> PathCond -> SymEval [([(Var, (Value, Type, Bool))], Context, PathCond)]
symEvalFields [] ctx pathCond = return [([], ctx, pathCond)]
symEvalFields (field : fields) ctx pathCond =
  foreachM (symEval (field ^. fieldInit, ctx, pathCond)) $ \(fieldVal, ctx', pathCond') ->
    foreachM (symEvalFields fields ctx' pathCond') $ \(evaledFields, ctx'', pathCond'') ->
      return [((field ^. fieldName, (fieldVal, field ^. fieldType, field ^. immutable)) : evaledFields, ctx'', pathCond'')]

symEvalList :: [Expr] -> Context -> PathCond -> SymEval [([Value], Context, PathCond)]
symEvalList [] ctx pathCond = return [([], ctx, pathCond)]
symEvalList (e : es) ctx pathCond =
  foreachM (symEval (e, ctx, pathCond)) $ \(val, ctx', pathCond') ->
    foreachM (symEvalList es ctx' pathCond') $ \(evaledList, ctx'', pathCond'') ->
      return [(val : evaledList, ctx'', pathCond'')]

-- | Return an unused address in the current context
nextAddr :: Context -> Addr
nextAddr ctx = maximum (M.keys (ctx ^. ctxObjs)) + 1

-- | Uncurry a three-argument function (useful for partial application)
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

-- | Try to find a method of the given name in the object at that address
findMethod :: Addr -> Var -> Context -> Maybe Method
findMethod addr name ctx = ctx ^? ctxObjs . ix addr . objMethods . ix name

callMethod :: Addr -> Method -> [Value] -> Context -> PathCond -> SymEval Results
callMethod addr mtd args ctx pathCond =
  let scope = M.fromList (zip (map fst (mtd ^. methodFormals))
                              args)
      ctx' = set ctxThis addr (set ctxScope scope ctx)
  in foreachM (symEval (mtd ^. methodBody, ctx', pathCond)) $ \(val, ctx'', pathCond') ->
       return [(val, set ctxThis (ctx ^. ctxThis) (set ctxScope (ctx ^. ctxScope) ctx''),
                pathCond')]

-- | `symEvalCall obj name args ...` symbolically evaluates a method call to method name on object obj
symEvalCall :: Value -> Var -> [Value] -> Context -> PathCond -> SymEval [(Value, Context, PathCond)]
symEvalCall (VRef addr) name args ctx pathCond
  | Just obj <- ctx ^. ctxObjs . at addr, obj ^. objAdversary =
      let newCalls = args : (ctx ^. ctxAdvCalls)
      in return [( Sym (AdversaryCall newCalls)
                 , set ctxAdvCalls newCalls ctx
                 , pathCond )]
  | Just mtd <- findMethod addr name ctx = callMethod addr mtd args ctx pathCond
  | otherwise = evalError ("Called non-existent method: " ++ name ++ "[" ++ show addr ++ "]") ctx
symEvalCall VNil name args ctx pathCond
  | Just mtd <- findMethod (ctx ^. ctxThis) name ctx =
      callMethod (ctx ^. ctxThis) mtd args ctx pathCond
  | Just mtd <- findMethod 0 name ctx =
      callMethod 0 mtd args ctx pathCond
  | otherwise = error "Call to non-existent method"
symEvalCall obj name args ctx pathCond =
  error $ "Bad method call[" ++ show obj ++ "]: " ++ name

lookupInTuple :: Value -> Value -> Value
lookupInTuple (VTuple vs) (VInt i)
  | fromInteger i < length vs = vs !! fromInteger i
  | otherwise = error "Invalid tuple index"
lookupInTuple tup (Sym sidx) = Sym (Proj tup (Sym sidx))
lookupInTuple (Sym sv) vidx = Sym (Proj (Sym sv) vidx)

isSymbolic :: Value -> Bool
isSymbolic (Sym _) = True
isSymbolic _ = False

symEval :: Config -> SymEval Results
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
symEval (ECVar eobj name eidx, ctx, pathCond) =
    foreachM (symEval (eobj, ctx, pathCond)) $ \(vobj, ctx', pathCond') ->
      foreachM (symEval (eidx, ctx', pathCond')) $ \(vidx, ctx'', pathCond'') ->
         return [(lookupECVar vobj name vidx ctx'', ctx'', pathCond'')]
symEval (EAssign (EVar x) rhs, ctx, pathCond) = do
  foreachM (symEval (rhs, ctx, pathCond)) $ \(vrhs, ctx', pathCond') ->
    return $ [(vrhs, updateVar x vrhs ctx', pathCond')]
symEval (EAssign (ECVar eobj name eidx) rhs, ctx, pathCond) =
  foreachM (symEval (rhs, ctx, pathCond)) $ \(vrhs, ctx', pathCond') ->
    foreachM (symEval (eobj, ctx', pathCond')) $ \(vobj, ctx'', pathCond'') ->
      foreachM (symEval (eidx, ctx'', pathCond'')) $ \(vidx, ctx''', pathCond''') ->
         return [(vrhs, updateECVar vobj name vidx vrhs ctx''', pathCond''')]
symEval (ESeq e1 e2, ctx, pathCond) = do
  foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    symEval (e2, ctx', pathCond')
symEval (EMethod name formals body, ctx, pathCond) = do
  return [(VNil, defineMethod name formals body ctx, pathCond)]
symEval (ECall (EConst VNil) "==" [e1, e2], ctx, pathCond) =
  foreachM (symEval (e1, ctx, pathCond)) $ \(v1, ctx', pathCond') ->
    foreachM (symEval (e2, ctx', pathCond')) $ \(v2, ctx'', pathCond'') ->
      if (isSymbolic v1 || isSymbolic v2) && (v1 /= v2)
      then return [ (VError, ctx'', Not (v1 :=: v2) : pathCond'')
                  , (VInt 1, ctx'', v1 :=: v2 : pathCond'')]
      else if v1 == v2
           then return [ (VInt 1, ctx'', pathCond'') ]
           else return [ (VError, ctx'', pathCond'') ]
symEval (ECall (EConst VNil) "!" [e], ctx, pathCond) = do
  foreachM (symEval (e, ctx, pathCond)) $ \(v, ctx', pathCond') ->
    case v of
      Sym sv -> return [ (VInt 1, ctx', v :=: VError : pathCond')
                       , (VError, ctx', Not (v :=: VError) : pathCond') ]
      VError -> return [ (VInt 1, ctx', pathCond') ]
      _ -> return [ (VError, ctx', pathCond') ]
symEval (ECall (EConst VNil) "&" [e1, e2], ctx, pathCond) = do
  foreachM (symEval (e1, ctx, pathCond)) handleCase
  where
    handleCase (VError, ctx', pathCond') = return [(VError, ctx', pathCond')]
    handleCase (Sym sv, ctx', pathCond') = do
      -- TODO: ask verifier if v can be proven to be Error/not-Error
      cfgs <- symEval (e2, ctx', Not (Sym sv :=: VError) : pathCond')
      return $ (VError, ctx', Sym sv :=: VError : pathCond') : cfgs
    handleCase (v, ctx', pathCond') = symEval (e2, ctx', pathCond')
symEval (ECall (EConst VNil) "|" [e1, e2], ctx, pathCond) = do
  foreachM (symEval (e1, ctx, pathCond)) handleCase
  where
    handleCase (VError, ctx', pathCond') = symEval (e2, ctx', pathCond')
    handleCase (Sym sv, ctx', pathCond') = do
      cfgs <- symEval (e2, ctx', (Sym sv :=: VError) : pathCond')
      return $ (Sym sv, ctx', Not (Sym sv :=: VError) : pathCond') : cfgs
    handleCase (v, ctx', pathCond') = return [(v, ctx', pathCond')]
symEval (ECall (EConst VNil) "adversary" [], ctx, pathCond) = do
  return [(VRef (nextAddr ctx)
          , ctxObjs . at (nextAddr ctx) ?~
            (Object { _objLocals = M.empty, _objMethods = M.empty
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
                                                      , _objAdversary = False
                                                      } $ ctx'
        ctx''' = set ctxThis (nextAddr ctx') ctx''
    in foreachM (symEval (body, ctx''', pathCond')) $ \(bodyVal, ctx'''', pathCond'') ->
      return [(VRef (nextAddr ctx'), set ctxThis (ctx' ^. ctxThis) ctx'''', pathCond'')]
symEval (e, ctx, pathCond) = error $ "unhandled case" ++ show e

evalSymEval :: MonadIO m => SymEval a -> m a
evalSymEval action = liftIO (fst <$> evalRWST (unSymEval action) () (SymEvalState))

symEval' :: MonadIO m => Config -> m Results
symEval' cfg = do
  results <- evalSymEval (symEval cfg)
  when (all ((== VError) . (\(a, _, _) -> a)) results) $
    liftIO $ putStrLn $ "WARN: Only VError as possible result of evaluation. Probably a bug?"
  return results

emptyCtx :: Context
emptyCtx = Context { _ctxObjs = M.fromList [(0, Object { _objLocals = M.empty
                                                       , _objMethods = M.empty
                                                       , _objAdversary = False })]
                   , _ctxThis = 0
                   , _ctxAdvCalls = []
                   , _ctxScope = M.empty }
