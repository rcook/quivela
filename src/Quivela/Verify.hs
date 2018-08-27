{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
module Quivela.Verify where

import Control.Applicative ((<$>))
import Control.Arrow (second)
import Control.Monad
import Control.Lens hiding (Context(..), rewrite)
import Control.Lens.At
import Control.Monad.RWS.Strict
import Control.Monad.List
import qualified Data.ByteString as BS
import Data.Generics hiding (Generic)
import Data.List
import Data.Function
import Data.Data
import Data.Maybe
import Data.Serialize (get, put, Serialize(..), encode, decode)
import Data.Typeable
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Set as S
import GHC.Generics (Generic)
import System.Directory
import System.Exit
import System.Microtimer
import System.IO
import System.IO.Temp
import System.Process

import Quivela.SymEval
import Quivela.Parse
import Quivela.VerifyPreludes

-- | Invariants; only the equality invariants are relational right now.
data Invariant = EqualInv (Addr -> Context -> Value) (Addr -> Context -> Value)
  -- ^ Equality of a value from the LHS and RHS contexts
  | ValidInv (Addr -> Context -> Addr -> Context -> Value)
  -- FIXME: this can be encoded as a universal invariant without parameters instead, we should
  -- remove this constructor
  | UnivInvariant [(Var, Type)] Expr
  -- ^ A quivela expression that must not return an error for any well-typed
  | Rewrite Expr Expr
  -- ^ Rewriting with an assumption. Currently we only support a single
  -- rewrite hint in each proof step
  | Admit
  -- ^ Don't check this step
  deriving Generic
-- FIXME: currently validity invariants look like relational invariants even though
-- they're not.


-- | Havoc a local variable if it's not an immutable variable
havocLocal :: Var -> Local -> Verify Local
havocLocal name l
  | not (view localImmutable l) = do
      fv <- freshVar name
      return $ set (localValue) (Sym (SymVar fv (l ^. localType))) l
  | otherwise = return l

-- | Havoc all non-immutable locals of an object
havocObj :: Object -> Verify Object
havocObj obj
  | obj ^. objAdversary = return obj -- this is a hack, since we currently don't
  -- support const annotations on global variables
  | otherwise = do
    newLocals <- mapM (\(name, loc) -> (name,) <$> havocLocal name loc)
      (M.toList (obj ^. objLocals))
    return (set objLocals (M.fromList newLocals) obj)

-- | Havoc all objects in a context
havocContext :: Context -> Verify Context
havocContext = everywhereM (mkM havocObj)

-- | Return an initial state for the verifier monad
newVerifyState :: IO VerifyState
newVerifyState = do
  (Just hin, Just hout, _, procHandle) <- createProcess $ (proc "z3" ["-in"]){ std_out = CreatePipe, std_in = CreatePipe, std_err = CreatePipe }
  hSetBuffering hin NoBuffering
  hSetBuffering hout NoBuffering
  hPutStrLn hin z3Prelude
  verificationCache <- do
    exists <- doesFileExist "cache.bin"
    if exists
    then do
      maybeCache <- decode <$> liftIO (BS.readFile "cache.bin")
      case maybeCache of
        Right cache -> return cache
        Left err -> return S.empty
    else return S.empty
  return VerifyState { _nextVar = M.empty
                     , _alreadyVerified = verificationCache
                     , _z3Proc = (hin, hout, procHandle) }

-- | Run a Verify action
runVerify :: VerifyEnv -> Verify a -> IO a
runVerify env action = do
  initState <- newVerifyState
  (res, state, _) <- runRWST (unVerify action) env initState
  return res

-- | Verification conditions
data VC = VC { _conditionName :: String
             -- ^ Purely for readability purposes when generating code for other solvers
             , _assumptions :: [Prop]
             , _goal :: Prop }
          deriving (Read, Ord, Eq, Data, Typeable)
makeLenses ''VC

emptyVC = VC { _conditionName = "vc"
             , _assumptions = []
             , _goal = PTrue }

-- Not technically a correct show instance, since it's not an inverse of `read`
instance Show VC where
  show (VC name assms goal) =
    unlines [ "\nAssumptions: "
            , intercalate "\n" (map show assms)
            , "Goal: "
            , show goal ]

-- | Throws an error if there is more than one result in the list. Used for
-- evaluating programs that are not supposed to have more than one result.
singleResult :: [Result] -> Result
singleResult [res] = res
singleResult ress = error $ "Multiple results: " ++ show ress

-- | Check if the assumptions are trivially contradictory
assumptionsContradictory :: [Prop] -> Bool
assumptionsContradictory assms =
  any (\asm -> case asm of
          Not p -> any (\asm' -> asm' == p) assms -- FIXME: this probably shouldn't be quadratic
          _ -> False) assms

-- | Check if the goal is trivial (equalities like x = x, a goal occurring as an assumption,
-- and having both P and (not P) as an assumption)
triviallyTrue :: VC -> Verify Bool
triviallyTrue vc
  | v1 :=: v1' <- vc ^. goal =
      return $ (v1 == v1') ||
      assumptionsContradictory (vc ^. assumptions)
  | (vc ^. goal) `elem` (vc ^. assumptions) = return True
  | otherwise = return False

-- | Rewrite all values that match the LHS of an equality invariant by its RHS.
rewriteInv :: Data p => Addr -> Context -> Addr -> Context -> Invariant -> p -> p
rewriteInv addrL ctxL addrR ctxR (EqualInv f g) x = everywhere (mkT replace) x
  where lhs = f addrL ctxL
        rhs = g addrR ctxR
        replace :: Value -> Value
        replace v | v == lhs = rhs
                  | otherwise= v
rewriteInv _ ctxL _ ctxR _ x = x

-- | Rewrite with a list of invariants. This ignores all non-equality invariants
rewriteEqInvs :: Data p => Addr -> Context -> Addr -> Context -> [Invariant] -> p -> p
rewriteEqInvs addrL ctxL addrR ctxR invs vc =
  foldr (rewriteInv addrL ctxL addrR ctxR) vc invs

typedValue :: Var -> Type -> Verify Value
typedValue name (TTuple ts) = VTuple <$> mapM (typedValue name) ts
typedValue name t = do
  freshName <- freshVar name
  return $ Sym (SymVar freshName t)

-- | Produce a list of symbolic values to use for method calls.
symArgs :: [(Var, Type)] -> Verify [Value]
symArgs args = mapM (uncurry typedValue) args

-- | Compute all relational proof obligations generated by an invariant
invToVC :: [Prop] -> Addr -> Result -> Addr -> Result -> Invariant -> Verify [VC]
invToVC assms addrL (_, ctxL, pathCondL) addrR (_, ctxR, pathCondR) inv =
  case inv of
    EqualInv f g -> return $
                    [emptyVC { _assumptions = nub $ pathCondL ++ pathCondR ++ assms
                             , _conditionName = "equalInvPreserved"
                             , _goal = f addrL ctxL :=: g addrR ctxR }]
    ValidInv f -> return $
      [VC { _assumptions = nub $ pathCondL ++ pathCondR ++ assms
          , _conditionName = "validInvPreserved"
          , _goal = Not (f addrL ctxL addrL ctxR :=: VError)
          }]
    UnivInvariant formals e -> return []

-- | Convert an invariant into assumptions. Note that for universal
-- invariants, this produces several assumptions.
invToAsm :: Result -> Result -> Invariant -> Verify [Prop]
invToAsm (VRef addrL, ctxL, pathCondL) (VRef addrR, ctxR, pathCondR) inv =
  case inv of
    EqualInv f g -> return [f addrL ctxL :=: g addrR ctxR]
    ValidInv f -> do
      let asm = Not (f addrL ctxL addrR ctxR :=: VError)
      return [asm]
    UnivInvariant formals e -> do
      args <- symArgs formals
      let scope = M.fromList (zip (map fst formals)
                                  (zip args (map snd formals)))
      pathsL <- symEval (e, set ctxThis addrL (set ctxScope scope ctxL), pathCondL)
      pathsR <- symEval (e, set ctxThis addrR (set ctxScope scope ctxR), pathCondR)
      let argNames = map (\(Sym (SymVar name t)) -> (name, t)) args
      foreachM (return $ pathsL ++ pathsR) $ \(res, ctxI, pathCondI) -> do
        return [Forall argNames (
                   (conjunction pathCondI) :=>: (Not (res :=: VError)))]
    _ -> return []

conjunction :: [Prop] -> Prop
conjunction [] = PTrue
conjunction [p] = p
conjunction ps = foldr1 (:&:) ps

-- | Return all non-relational proof obligations generated by invariants
invToVCnonRelational :: [Prop] -> Addr -> Result -> Invariant -> Verify [VC]
invToVCnonRelational assms addr res@(v, ctx, pathCond) inv =
  case inv of
    UnivInvariant formals e -> do
      args <- symArgs formals
      let scope = M.fromList (zip (map fst formals)
                                  (zip args (map snd formals)))
      paths <- symEval (e, set ctxThis addr (set ctxScope scope ctx), pathCond)
      foreachM (return $ paths) $ \(res, ctxI, pathCondI) ->
        return $ [VC { _assumptions = nub $ pathCondI ++ assms
                     , _conditionName = "univInvPreserved"
                     , _goal = Not (res :=: VError) }]
    _ -> return []

-- | Generate the verification conditions for two sets of results (i.e.
-- configurations returned by evaluating a method call with symbolic arguments
-- in a havoced context). Also takes the old havoced environments as arguments
-- to turn invariants into assumptions.
resultsToVCs :: [Invariant] -> Result -> Results -> Result -> Results -> Verify [VC]
resultsToVCs invs old@(VRef addr1, ctxH, pathCondH) ress1 old'@(VRef addr1', ctxH', pathCondH') ress1' = do
  -- Some invariants aren't really relational and hence we don't need to check them for each pair of
  -- of paths:
  assms <- concat <$> mapM (invToAsm old old') invs
  lhsInvVCs <- foreachM (return ress1) $ \res1 -> do
    concat <$> mapM (invToVCnonRelational assms addr1 res1) invs
  rhsInvVCs <- foreachM (return ress1') $ \res1' -> do
    concat <$> mapM (invToVCnonRelational assms addr1' res1') invs
  relationalVCs <-
    foreachM (return ress1) $ \res1@(v1, ctx1, pc1) ->
      foreachM (return ress1') $ \res1'@(v1', ctx1', pc1') -> do
        let simp = rewriteEqInvs addr1 ctx1 addr1' ctx1' invs
            simp' = rewriteEqInvs addr1 ctx1 addr1' ctx1' invs
        let vcRes = VC { _assumptions = nub $ assms ++ map simp' (nub $ pc1 ++ pc1' ++ assms)
                       , _conditionName = "resultsEq"
                       , _goal = simp' (v1 :=: v1') }
        invVCs <-
          if ctx1 == ctxH && ctx1' == ctxH'
          then return []
          else concat <$> mapM (fmap (map simp) .
                                invToVC assms addr1 res1 addr1' res1') invs
        -- Require that adversary was called with same values:
        let vcAdv = VC { _assumptions = nub $ assms ++ map simp' (nub $ pc1 ++ pc1' ++ assms)
                       , _conditionName = "advCallsEq"
                       , _goal = simp' $ Sym (AdversaryCall (ctx1 ^. ctxAdvCalls)) :=:
                                         Sym (AdversaryCall (ctx1' ^. ctxAdvCalls)) }
        return $ vcRes : vcAdv : invVCs
  return $ relationalVCs ++ lhsInvVCs ++ rhsInvVCs


-- | Convenience function for validity invariants on the LHS
validLHS :: (Addr -> Context -> Value) -> Invariant
validLHS f = ValidInv (\a1 ctx1 _ _ -> f a1 ctx1)

validRHS :: (Addr -> Context -> Value) -> Invariant
validRHS f = ValidInv (\_ _ a2 ctx2 -> f a2 ctx2)

-- | Collect non-trivial verification conditions for a given method, invariants and arguments
methodEquivalenceVCs :: Method -> [Invariant] -> [Value] -> Result -> Result -> Verify [VC]
methodEquivalenceVCs mtd invs args
                     (VRef a1, ctx1, pathCond1)
                     (VRef a1', ctx1', pathCond1') = do
  ctxH1 <- havocContext ctx1
  ctxH1' <- havocContext ctx1'
  results <- symEval (ECall (EConst (VRef a1)) (mtd ^. methodName) (map EConst  args), ctxH1, pathCond1)
  results' <- symEval (ECall (EConst (VRef a1')) (mtd ^. methodName) (map EConst  args), ctxH1', pathCond1')
  vcs <- resultsToVCs invs (VRef a1, ctxH1, pathCond1) results (VRef a1', ctxH1', pathCond1') results'
  -- debug $ "VCs before pruning: " ++ show (length vcs)
  filterM (\vc -> do
                   trivial <- triviallyTrue vc
                   if trivial
                     then do
                     -- debug $ "Discarding VC as trivial: " ++ show vc
                     return False
                     else return True) vcs


-- | Print out debugging information.
debug :: (MonadIO m) => String -> m ()
debug = liftIO . putStrLn -- TODO: move this to a utility module or so

-- | Helper function for writing equality invariants. Produces an exception
-- if the chain of fields doesn't exist in the given context.
getField :: [Var] -> Addr -> Context -> Value
getField [] _ _ = error "Empty list of fields"
getField [x] addr ctx
  | Just v <- ctx ^? ctxObjs . ix addr . objLocals . ix x . localValue = v
  | otherwise = error $ "getField: No such field: " ++ x
getField (x : xs) addr ctx
  | Just (VRef addr') <- ctx ^? ctxObjs . ix addr . objLocals . ix x . localValue =
      getField xs addr' ctx
  | otherwise = error $ "Non-reference in field lookup"

-- | Find the shared methods between two objects in their respective contexts
sharedMethods :: Addr -> Context -> Addr -> Context -> [Method]
sharedMethods addrL ctxL addrR ctxR
  | Just objL <- ctxL ^? ctxObjs . ix addrL,
    Just objR <- ctxR ^? ctxObjs . ix addrR =
  let mtdsL = objL ^. objMethods
      mtdsR = objR ^. objMethods
      sharedNames = M.keys mtdsL `intersect` M.keys mtdsR
  -- TODO: check that there are no extraneous methods and that they
  -- take the same number (and type) of arguments
  in map (fromJust . (`M.lookup` mtdsL)) sharedNames


-- | A monad for emitting code for external tools. In addition to state
-- to keep track of fresh variables, this also includes a writer monad
-- to collect all emitted lines.
newtype Emitter a = Emitter { unEmitter :: RWST () [String] EmitterState IO a }
  deriving (Functor, Applicative, Monad, MonadState EmitterState,
            MonadWriter [String])

data EmitterState = EmitterState { _nextEmitterVar :: M.Map String Integer
                                 , _varTranslations :: M.Map String String
                                 , _usedVars :: [(String, String)]
                                 -- ^ Stores generated fresh variables and their type in the solver
                                 }
  deriving (Read, Show, Eq, Ord, Data, Typeable)

makeLenses ''EmitterState

-- TODO: merge with previous implementation
freshEmitterVar :: String -> String -> Emitter String
freshEmitterVar prefix' typ = do
  let prefix = filter (`notElem` "?") prefix'
  last <- use (nextEmitterVar . at prefix)
  case last of
    Just n -> do
      nextEmitterVar . ix prefix %= (+1)
      let varName = prefix ++ show n
      usedVars %= ((varName, typ) :)
      return varName
    Nothing -> do
      modify (nextEmitterVar . at prefix ?~ 0)
      freshEmitterVar prefix typ

emit :: String -> Emitter ()
emit = tell . (:[])


-- | Translate a variable name. Caches the result for each variable
-- name so when called with the same variable name again, it will return the same result
-- to make sure that each variable receives a fresh identifier and other occurrences of
-- the same variable receive the same name.
translateVar :: String -> String -> Emitter String
translateVar v typ = do
  translated <- gets (\s -> s ^? (varTranslations . ix v))
  case translated of
    Just tv -> return tv
    Nothing -> do
      tv <- freshEmitterVar v typ -- TODO: think if we really need something fresh here, since
      -- we're only using this with fresh variables generated by the VCG
      modify (\s -> varTranslations . at v ?~ tv $ s)
      return tv

-- | Collect all symbolic variables occurring in some data
collectSymVars :: Data p => p -> [(Var, Type)]
collectSymVars vc = nubBy ((==) `on` fst) . map toTup $ listify isSymVar vc
  where isSymVar (SymVar _ _) = True
        isSymVar _ = False
        toTup (SymVar x t) = (x, t)

symVarName :: SymValue -> Var
symVarName (SymVar n t) = n

-- | Type class for things that can be converted into Dafny terms
class ToDafny a where
  toDafny :: a -> Emitter String

listToDafny :: ToDafny a => [a] -> Emitter String
listToDafny [] = return "LNil()"
listToDafny (v : vs) = do
  car <- toDafny v
  cdr <- listToDafny vs
  return $ "Cons(" ++ car ++ ", " ++ cdr ++ ")"

instance ToDafny a => ToDafny [a] where
  toDafny = listToDafny

instance ToDafny Value where
  toDafny = valueToDafny

instance (ToDafny a, ToDafny b) => ToDafny (a, b) where
  toDafny (a, b) = do
    car <- toDafny a
    cdr <- toDafny b
    return $ "Pair(" ++ car ++ ", " ++ cdr ++ ")"

concatM = fmap concat . sequence

instance ToDafny SymValue where
  toDafny = symValToDafny

dafnyFunCall :: String -> [String] -> String
dafnyFunCall f args = f ++ "(" ++ intercalate ", " args ++ ")"

symValToDafny :: SymValue -> Emitter String
symValToDafny (SymVar s t) = translateVar s "Value"
symValToDafny (Insert k v m) =
  dafnyFunCall "Insert" <$> mapM toDafny [k, v, m]
symValToDafny (Lookup k m) =
  dafnyFunCall "Lookup" <$> mapM toDafny [k, m]
symValToDafny (Proj tup idx) =
  dafnyFunCall "Proj" <$> mapM toDafny [tup, idx]
symValToDafny (AdversaryCall advCalls) =
  dafnyFunCall "Adversary" . (:[]) <$> toDafny advCalls
symValToDafny (Add e1 e2) =
  dafnyFunCall "Add" <$> mapM toDafny [e1, e2]
symValToDafny (Mul e1 e2) =
  dafnyFunCall "Mul" <$> mapM toDafny [e1, e2]
symValToDafny (Sub e1 e2) =
  dafnyFunCall "Sub" <$> mapM toDafny [e1, e2]
symValToDafny (Div e1 e2) =
  dafnyFunCall "Div" <$> mapM toDafny [e1, e2]
symValToDafny (Le e1 e2) =
  dafnyFunCall "Le" <$> mapM toDafny [e1, e2]
symValToDafny (ITE tst thn els) = do
  tstDafny <- toDafny tst
  [thnDafny, elsDafny] <- mapM toDafny [thn, els]
  return $ "(if " ++ tstDafny ++ " then " ++ thnDafny ++ " else " ++ elsDafny ++ ")"

valueToDafny :: Value -> Emitter String
valueToDafny (VInt i) = return $ "Int(" ++ show i ++ ")"
valueToDafny (VTuple vs) = concatM [pure "Tuple(", toDafny vs, pure ")"]
valueToDafny (VMap m) = concatM [pure "Map(", toDafny (M.toList m), pure ")"]
valueToDafny (VRef a) = return $ "Ref(" ++ show a ++ ")"
valueToDafny VNil = return "Nil()"
valueToDafny VError = return "Error()"
valueToDafny (Sym sv) = symValToDafny sv

instance ToDafny Prop where
  toDafny = propToDafny

propToDafny :: Prop -> Emitter String
propToDafny (x :=: y) = concatM [valueToDafny x, pure " == ", valueToDafny y]
propToDafny (Not (x :=: y)) = concatM [toDafny x, pure " != ", toDafny y]
propToDafny (Not p) = concatM [pure "!", pure "(", propToDafny p, pure ")"]
propToDafny PTrue = return "true"
propToDafny PFalse = return "false"
propToDafny (p1 :&: p2) = concatM [ pure "("
                                  , toDafny p1
                                  , pure ") && ("
                                  , toDafny p2
                                  , pure ")" ]
propToDafny (p1 :=>: p2) = concatM [ pure "(", toDafny p1
                                   , pure ") ==> ("
                                   , toDafny p2
                                   , pure ")" ]
propToDafny (Forall [] p) = toDafny p
propToDafny (Forall formals p) =
  concatM [ pure "forall "
          , intercalate ", " . map ((++ ": Value")) <$> mapM (\(x, t) -> translateVar x "Value") formals
          , pure " :: "
          , toDafny p ]

asmToDafny :: Prop -> Emitter ()
asmToDafny p =
  emit . ("  requires "++) =<< propToDafny p

vcToDafny :: VC -> Emitter ()
vcToDafny vc = do
  lemName <- (`freshEmitterVar` "_unused") $ vc ^. conditionName
  lemArgs <- mapM (\(x, t) -> translateVar x "Value") $ collectSymVars vc
  emit $ "lemma " ++ lemName ++ "(" ++ intercalate ", " (map (++ ": Value") lemArgs) ++ ")"
  mapM_ asmToDafny (vc ^. assumptions)
  dafnyGoal <- propToDafny $ vc ^. goal
  emit $ "  ensures " ++ dafnyGoal
  emit $ "{ LookupSame(); LookupDifferent(); }"

initialEmitterState = EmitterState { _nextEmitterVar = M.empty
                                   , _usedVars = []
                                   , _varTranslations = M.empty }

runEmitter :: MonadIO m => Emitter a -> m (a, [String])
runEmitter action = liftIO $ evalRWST (unEmitter action) () initialEmitterState

-- | Try to verify a list of verification conditions with dafny
checkWithDafny :: MonadIO m => [VC] -> m Bool
checkWithDafny [] = return True
checkWithDafny vcs = do
  debug $ "Checking " ++ show (length vcs) ++ " VCs with Dafny"
  (_, lines) <- runEmitter $ do
    emit dafnyPrelude
    mapM_ vcToDafny vcs
  tempFile <- liftIO $ writeTempFile "." "dafny-vc.dfy" (unlines lines)
  debug $ "Dafny code written to " ++ tempFile
  (code, out, err) <- liftIO $ readCreateProcessWithExitCode (proc "time"
    ["dafny", "/compile:0", tempFile]) ""
  if code == ExitSuccess
    then do
      debug "Verification succeeded"
      debug err
      return True
    else do
      debug $ "Verification failed\n:stdout:\n" ++ out ++ "\nstderr:\n" ++ err
      return False

-- | Type class for values that can be converted into Z3 terms/formulas
class ToZ3 a where
  toZ3 :: a -> Emitter String

z3Call :: String -> [String] -> String
z3Call fun args = "(" ++ fun ++ " " ++ intercalate " " args ++ ")"

-- | Return an s-expression of applying the first argument to a list things that
-- can be converted to z3 expressions
z3CallM :: (ToZ3 a) => String -> [a] -> Emitter String
z3CallM fun args = z3Call fun <$> mapM toZ3 args

propToZ3 :: Prop -> Emitter String
propToZ3 PTrue = return "true"
propToZ3 PFalse = return "false"
propToZ3 (Not p) = z3CallM "not" [p]
propToZ3 (x :=: y) = z3CallM "="  [x, y]
propToZ3 (x :=>: y) = z3CallM "=>" [x, y]
propToZ3 (x :&: y) = z3CallM "and" [x, y]
propToZ3 (Forall [] p) = toZ3 p
propToZ3 (Forall formals p) = do
  argNames <- mapM (\(x, t) -> translateVar x "Value") formals
  concatM [ pure "(forall ("
          , pure $ intercalate " " (map (\n -> "(" ++ n ++ " Value)") argNames)
          , pure ") "
          , toZ3 p
          , pure ")" ]

instance ToZ3 Prop where
  toZ3 = propToZ3

-- To make life easier for Z3, we keep all the data types involved monomorphic,
-- so we have separate types in Z3 for values, lists of values, and lists of lists of values:
valuesToZ3 :: [Value] -> Emitter String
valuesToZ3 [] = return "nil"
valuesToZ3 (v : vs) = z3Call "cons" <$> sequence [toZ3 v, valuesToZ3 vs]

valuessToZ3 :: [[Value]] -> Emitter String
valuessToZ3 [] = return "nils"
valuessToZ3 (vs : vss) = z3Call "conss" <$> sequence [valuesToZ3 vs, valuessToZ3 vss]

valueToZ3 :: Value -> Emitter String
valueToZ3 (VInt i) = return $ z3Call "VInt" [show i]
valueToZ3 VError = return "VError"
valueToZ3 (VTuple vs) = z3Call "VTuple" <$> sequence [valuesToZ3 vs]
valueToZ3 (VMap map) = freshEmitterVar "map" "Value" -- TODO: map same maps to same variable
valueToZ3 VNil = return "VNil"
valueToZ3 (VRef addr) = return $ z3Call "VRef" [show addr]
valueToZ3 (Sym sv) = symValueToZ3 sv

symValueToZ3 :: SymValue -> Emitter String
symValueToZ3 (SymVar x t) =
  case t of
    TInt -> z3Call "VInt" <$> sequence [translateVar x "Int"]
    _ -> translateVar x "Value"
symValueToZ3 (Insert k v m) = z3CallM "insert" [k, v, m]
symValueToZ3 (Lookup k m) = z3CallM "lookup" [k, m]
symValueToZ3 (AdversaryCall vss) = z3Call "adversary" <$> sequence [valuessToZ3 vss]
symValueToZ3 (Proj tup idx) = z3CallM "proj" [tup, idx]
symValueToZ3 (Add v1 v2) = z3CallM "add" [v1, v2]
symValueToZ3 (Sub v1 v2) = z3CallM "sub" [v1, v2]
symValueToZ3 (Mul v1 v2) = z3CallM "mul" [v1, v2]
symValueToZ3 (Div v1 v2) = z3CallM "divi" [v1, v2]
symValueToZ3 (Le v1 v2) = z3CallM "le" [v1, v2]
symValueToZ3 (ITE tst thn els) = z3Call "ite" <$> sequence [toZ3 tst, toZ3 thn, toZ3 els]

vcToZ3 :: VC -> Emitter ()
vcToZ3 vc = do
  emit $ ";; " ++ (vc ^. conditionName)
  translatedAssms <- mapM toZ3 (vc ^. assumptions)
  goalProp <- toZ3 (vc ^. goal)
  vars <- use usedVars
  forM vars $ \(var, typ) ->
    emit $ z3Call "declare-const" [var, typ]
  mapM (\asm -> emit (z3Call "assert" [asm])) translatedAssms
  emit $ z3Call "assert" [z3Call "not" [goalProp]]

sendToZ3 :: String -> Verify ()
sendToZ3 line = do
  (hin, _, _) <- use z3Proc
  liftIO $ hPutStrLn hin line

readLineFromZ3 :: Verify String
readLineFromZ3 = do
  (_, hout, _) <- use z3Proc
  liftIO $ hGetLine hout

checkWithZ3 :: VC -> Verify Bool
checkWithZ3 vc = do
  (_, vcLines) <- runEmitter $ vcToZ3 vc
  sendToZ3 "(push)"
  sendToZ3 (unlines vcLines)
  sendToZ3 "(check-sat)"
  answer <- readLineFromZ3
  sendToZ3 "(pop)"
  return $ "unsat" `isInfixOf` answer

instance ToZ3 Value where
  toZ3 = valueToZ3

instance ToZ3 SymValue where
  toZ3 = symValueToZ3

writeToZ3File :: VC -> Verify FilePath
writeToZ3File vc = do
  (_, vcLines) <- runEmitter $ vcToZ3 vc
  tempFile <- liftIO $ writeTempFile "." "z3-vc.smt2" $ unlines $ z3Prelude : vcLines ++ ["(check-sat)"]
  return tempFile

-- | Verify conditions with external solvers and return unverified conditions
checkVCs :: [VC] -> Verify [VC]
checkVCs [] = return []
checkVCs vcs = do
  debug $ show (length vcs) ++ " verification conditions"
  (t, vcs') <- time $ filterM (fmap not . checkWithZ3) vcs
  when (not . null $ vcs') $ do
    debug $ "Remaining VCs in Z3 files: "
    mapM_ (\vc -> writeToZ3File vc >>= \f -> liftIO (debug f)) vcs'
  debug $ show (length vcs') ++ " VCs left after checking with Z3 (" ++ formatSeconds t ++ ")"
  dafnyRes <- checkWithDafny vcs'
  -- currently we don't have a way to efficiently check just one VC with Dafny, so this
  -- is all or nothing:
  if dafnyRes then return [] else return vcs'

checkEqv :: Bool -> Expr -> [Invariant] -> Expr -> Expr -> Verify [(Var, [VC])]
checkEqv useSolvers prefix [Admit] lhs rhs = do
  -- debug $ "Skipping proof step: " ++ show lhs ++ " ~ " ++ show rhs
  return []
checkEqv useSolvers prefix [Rewrite from to] lhs rhs =
  if lhs' == rhs then return []
  else error $ "Invalid rewrite step:\n" ++ show lhs' ++ "\n/=\n" ++ show rhs
  where lhs' = rewriteExpr from to lhs
checkEqv useSolvers prefix invs lhs rhs = do
  cached <- S.member (lhs, rhs) <$> use alreadyVerified
  if cached
  then do
    debug "Skipping cached verification step"
    return []
  else do
    (_, prefixCtx, pathCond) <- fmap singleResult .
                                symEval $ (prefix, emptyCtx, [])
    res1@(VRef a1, ctx1, _) <- singleResult <$> symEval (lhs, prefixCtx, pathCond)
    res1'@(VRef a1', ctx1', _) <- singleResult <$> symEval (rhs, prefixCtx, pathCond)
    -- check that invariants hold initially
    invLHS <- concat <$> mapM (invToVCnonRelational [] a1 res1) invs
    invRHS <- concat <$> mapM (invToVCnonRelational [] a1' res1') invs
    invsRel <- concat <$> mapM (invToVC [] a1 res1 a1' res1') invs
    remainingInvVCs <- checkVCs (invLHS ++ invRHS ++ invsRel)
    let mtds = sharedMethods a1 ctx1 a1' ctx1'
    (t, remainingVCs) <- fmap (second ([("_invsInit", remainingInvVCs)] ++)) . time $ forM mtds $ \mtd -> do
      debug $ "Checking method: " ++ mtd ^. methodName
      args <- symArgs (mtd ^. methodFormals)
      vcs <- methodEquivalenceVCs mtd invs args res1 res1'
      verificationResult <- if useSolvers then checkVCs vcs else return vcs

      return (mtd ^. methodName, verificationResult)
    if (not . all (null . snd) $ remainingVCs)
    then do
      liftIO $ putStrLn "Verification failed"
      liftIO $ print remainingVCs
    else do
      cacheVerified lhs rhs
      liftIO . putStrLn $ "Verification succeeded in " ++ formatSeconds t
    return remainingVCs

-- | Mark a pair of expressions as successfully verified in the cache
cacheVerified :: Expr -> Expr -> Verify ()
cacheVerified lhs rhs = do
  alreadyVerified %= S.insert (lhs, rhs)
  verified <- use alreadyVerified
  liftIO $ BS.writeFile "cache.bin" (encode verified)

-- | Check two quivela files for equivalence using a list of invariants. The
-- first quivela file contains shared global variables and method definitions
-- (The other two programs are evaluated in the context resulting from
-- evaluating the prefix file). If the first argument is False, external solvers
-- will not be used.
checkEqvFile :: Bool -> FilePath -> [Invariant] -> FilePath -> FilePath
         -> Verify [(Var, [VC])]
checkEqvFile verify prefixFile invs lhsFile rhsFile = do
  prefix <- parseFile prefixFile
  lhs <- parseFile lhsFile
  rhs <- parseFile rhsFile
  checkEqv verify prefix invs lhs rhs

-- | Quivela proofs are a series of equivalent expressions and a list of
-- invariants that are needed to verify this step.
type Steps = [(Expr, [Invariant])]

foldStepsM :: Monad m => ([Invariant] -> Expr -> Expr -> a -> m a) -> a -> Steps -> m a
foldStepsM f init [] = return init
foldStepsM f init ((lhs, invs) : steps) = foldStepsM' steps lhs invs init
  where foldStepsM' [] lhs invs acc = return acc
        foldStepsM' ((rhs, invsR) : steps) lhs invs acc = do
          res <- f invs lhs rhs acc
          foldStepsM' steps rhs invsR res

mapStepsM :: Monad m => ([Invariant] -> Expr -> Expr -> m a) -> Steps -> m [a]
mapStepsM f = foldStepsM (\invs lhs rhs prev -> (prev ++) . (:[]) <$> f invs lhs rhs) []

-- | Check given list of steps and return a list of unverified VCs for each step
checkSteps :: Expr -> Steps -> Verify [[(Var, [VC])]]
checkSteps prefix = mapStepsM (checkEqv True prefix)

-- | @'rewriteExpr' from to e@ rewrites all occurrences of @from@ in @e@ by @to@
-- TODO: take bound variables into account
rewriteExpr :: Expr -> Expr -> Expr -> Expr
rewriteExpr from to e = everywhere (mkT replace) e
  where replace :: Expr -> Expr
        replace e' | e' == from = to
                   | otherwise = e'

-- | Convenience function for expression that both sides agree on looking
-- up a series of fields. @[a, b, c]@ represents looking up field @a.b.c@.
fieldsEqual :: [Var] -> [Var] -> Invariant
fieldsEqual fieldsL fieldsR = EqualInv (getField fieldsL) (getField fieldsR)

-- | Like 'fieldsEqual' but looking up the same fields on both sides.
fieldEqual :: [Var] -> Invariant
fieldEqual fields = fieldsEqual fields fields

clearCache :: IO ()
clearCache = do
  exists <- doesFileExist "cache.bin"
  when exists $ removeFile "cache.bin"

-- | One part of a quivela proof, which is either an expression, or a proof hint.
-- An followed by a hint and another expression is verified using that hint,
-- while two expressions in a row are verified without additional proof hints.
-- The steps are chained automatically, e.g. @[e1, h1, e2, e3]@ will result in verifying
-- @e1 ~[h1] e2 ~ e3@
data ProofPart = Prog Expr | Hint [Invariant]

-- | Convert a series of proof parts into a sequence of steps
toSteps :: [ProofPart] -> Steps
toSteps [] = []
toSteps [Prog exp] = [(exp, [])]
toSteps (Prog exp : Prog exp' : steps') = (exp, []) : toSteps (Prog exp' : steps')
toSteps (Prog exp : Hint invs : steps') = (exp, invs) : toSteps steps'
toSteps _ = error "Invalid sequence of steps"

-- | A handy alias for cons; this makes a sequence of proof steps look more like
-- an actual equivalence relation.
(~~) :: a -> [a] -> [a]
x ~~ y = x : y

infixr 5 ~~

-- | Like '~~' but using a nicer-looking unicode operator instead.
(≈) :: a -> [a] -> [a]
x ≈ y = x : y

infixr 5 ≈

nop :: Expr
nop = ENop
