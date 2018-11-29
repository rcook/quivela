-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}

module Quivela.Verify
  ( (≈)
  , clearCache
  , fieldEqual
  , fieldsEqual
  , proveStep
  , runVerify
  , toSteps
  ) where

import Control.Applicative ((<$>), (<|>))
import Control.Arrow (second)
import qualified Control.Lens as C
import Control.Lens ((%=), (.=), (?~), (^.), (^?), at, set, use, view)
import Control.Lens.At (ix)
import Control.Monad.RWS.Strict
  ( MonadIO
  , MonadState
  , MonadWriter
  , RWST
  , censor
  , evalRWST
  , filterM
  , foldM
  , forM
  , gets
  , liftIO
  , listen
  , modify
  , runRWST
  , tell
  , unless
  , when
  )
import qualified Data.ByteString as BS
import Data.Data (Data)
import Data.Function (on)
import Data.Generics
  ( everythingWithContext
  , everywhere
  , everywhereBut
  , everywhereM
  , extQ
  , listify
  , mkM
  , mkQ
  , mkT
  )
import Data.List ((\\), intercalate, intersect, isInfixOf, nub, nubBy)
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Data.Maybe (catMaybes, fromJust, listToMaybe)
import Data.Serialize (Serialize(..), decode, encode, get, put)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import Debug.Trace (trace)
import GHC.Generics (Generic)
import System.Directory (doesFileExist, removeFile)
import System.Exit (ExitCode(ExitSuccess))
import System.IO (BufferMode(NoBuffering), hGetLine, hPutStrLn, hSetBuffering)
import System.IO.Temp (writeTempFile)
import qualified System.Timer as Timer
import System.Process
  ( StdStream(CreatePipe)
  , createProcess
  , proc
  , readCreateProcessWithExitCode
  , std_err
  , std_in
  , std_out
  )

import Quivela.Diff (applyDiffs)
import qualified Quivela.Language as L
import Quivela.Language
  ( Addr
  , Context
  , Expr(..)
  , Local
  , Method
  , MethodKind(..)
  , Object
  , PathCond(..)
  , ProofHint(..)
  , ProofPart(..)
  , Prop(..)
  , SymValue(..)
  , Type(..)
  , pattern VRef
  , Value(..)
  , Var
  )
import qualified Quivela.Parse as P
import qualified Quivela.SymEval as E
import Quivela.SymEval
  ( Result
  , Results
  , Verify
  , VerifyEnv
  , VerifyState(..)
  , debug
  , symEval
  )
import Quivela.Util (foreachM)
import Quivela.VerifyPreludes (z3Prelude)

-- | A type class for types that only support equality partially. Whenever @(a === b) == Just x@,
-- then the boolean x indicates that a and b are equal/unequal. Otherwise, it cannot be determined
-- if the two values are equal
class PartialEq a where
  (===) :: a -> a -> Maybe Bool

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

-- | Verification conditions
data VC = VC
  { _conditionName :: String
             -- ^ Purely for readability purposes when generating code for other solvers
  , _assumptions :: [Prop]
  , _goal :: Prop
  } deriving (Read, Ord, Eq, Data, Typeable)

C.makeLenses ''VC

data SolverCmd
  = Raw String
  | NewVar String
           String
  | NewAssm String
  deriving (Read, Show, Eq, Ord, Data, Typeable)

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

data EmitterState = EmitterState
  { _nextEmitterVar :: M.Map String Integer
  , _varTranslations :: M.Map String String
  , _usedVars :: [(String, String)]
                                 -- ^ Stores generated fresh variables and their type in the solver
  , _emitterPrefixCtx :: Context
                                 -- ^ We make the context of the "prefix"
                                 -- program of a proof available to emitters so
                                 -- they can generate output for uninterpreted
                                 -- functions, etc.
  } deriving (Read, Show, Eq, Ord, Data, Typeable)

C.makeLenses ''EmitterState

-- | Havoc a local variable if it's not an immutable variable
havocLocal :: Var -> Local -> Verify Local
havocLocal name l
  | not (view L.localImmutable l) = do
    fv <- E.freshVar name
    return $ set (L.localValue) (Sym (SymVar fv (l ^. L.localType))) l
  | otherwise = return l

-- | Havoc all non-immutable locals of an object
havocObj :: Object -> Verify Object
havocObj obj
  | obj ^. L.objAdversary = return obj -- this is a hack, since we currently don't
  -- support const annotations on global variables
  | otherwise = do
    newLocals <-
      mapM
        (\(name, loc) -> (name, ) <$> havocLocal name loc)
        (M.toList (obj ^. L.objLocals))
    return (set L.objLocals (M.fromList newLocals) obj)

-- | Havoc all objects in a context
havocContext :: Context -> Verify Context
havocContext = everywhereM (mkM havocObj)

-- | Return an initial state for the verifier monad
newVerifyState :: IO VerifyState
newVerifyState = do
  (Just hin, Just hout, _, procHandle) <-
    createProcess $
    (proc "z3" ["-in"])
      {std_out = CreatePipe, std_in = CreatePipe, std_err = CreatePipe}
  hSetBuffering hin NoBuffering
  hSetBuffering hout NoBuffering
  hPutStrLn hin z3Prelude
  verificationCache <-
    do exists <- doesFileExist "cache.bin"
       if exists
         then do
           maybeCache <- decode <$> liftIO (BS.readFile "cache.bin")
           case maybeCache of
             Right cache -> return cache
             Left err -> return S.empty
         else return S.empty
  return
    VerifyState
      { _alreadyVerified = verificationCache
      , _nextVar = M.empty
      , _verifyPrefixCtx = L.emptyCtx
      , _z3Proc = (hin, hout, procHandle)
      }

-- | Run a Verify action
runVerify :: VerifyEnv -> Verify a -> IO a
runVerify env action = do
  initState <- newVerifyState
  (res, state, _) <- runRWST (E.unVerify action) env initState
  return res

emptyVC = VC {_conditionName = "vc", _assumptions = [], _goal = PTrue}

-- Not technically a correct show instance, since it's not an inverse of `read`
instance Show VC where
  show (VC name assms goal) =
    unlines
      [ "\nName: " ++ name
      , "\nAssumptions: "
      , intercalate "\n" (map show assms)
      , "Goal: "
      , show goal
      ]

-- | Check if the assumptions are trivially contradictory
assumptionsContradictory :: [Prop] -> Bool
assumptionsContradictory assms =
  any
    (\asm ->
       case asm of
         Not p -> any (\asm' -> asm' == p) assms -- FIXME: this probably shouldn't be quadratic
         _ -> False)
    assms

-- | Check if the goal is trivial (equalities like x = x, a goal occurring as an assumption,
-- and having both P and (not P) as an assumption)
triviallyTrue :: VC -> Verify Bool
triviallyTrue vc
  | v1 :=: v1' <- vc ^. goal =
    return $ (v1 == v1') || assumptionsContradictory (vc ^. assumptions)
  | (vc ^. goal) `elem` (vc ^. assumptions) = return True
  | otherwise = return False

-- | Rewrite all values that match the LHS of an equality invariant by its RHS.
rewriteInv ::
     Data p => Addr -> Context -> Addr -> Context -> ProofHint -> p -> p
rewriteInv addrL ctxL addrR ctxR (EqualInv f g) x = everywhere (mkT replace) x
  where
    lhs = f addrL ctxL
    rhs = g addrR ctxR
    replace :: Value -> Value
    replace v
      | v == lhs = rhs
      | otherwise = v
rewriteInv _ ctxL _ ctxR _ x = x

-- | Rewrite with a list of invariants. This ignores all non-equality invariants
rewriteEqInvs ::
     Data p => Addr -> Context -> Addr -> Context -> [ProofHint] -> p -> p
rewriteEqInvs addrL ctxL addrR ctxR invs vc =
  foldr (rewriteInv addrL ctxL addrR ctxR) vc invs

-- | Compute all relational proof obligations generated by an invariant
invToVC ::
     [Prop] -> Addr -> Result -> Addr -> Result -> ProofHint -> Verify [VC]
invToVC assms addrL (_, ctxL, pathCondL) addrR (_, ctxR, pathCondR) inv =
  case inv of
    EqualInv f g ->
      return $
      [ emptyVC
          { _assumptions = nub $ pathCondL ++ pathCondR ++ assms
          , _conditionName = "equalInvPreserved"
          , _goal = f addrL ctxL :=: g addrR ctxR
          }
      ]
    _ -> return []

-- | Convert an invariant into assumptions. Note that for universal
-- invariants, this produces several assumptions.
invToAsm :: Result -> Result -> ProofHint -> Verify [Prop]
invToAsm (VRef addrL, ctxL, pathCondL) (VRef addrR, ctxR, pathCondR) inv =
  case inv of
    EqualInv f g -> return [f addrL ctxL :=: g addrR ctxR]
    _ -> return []
invToAsm (v1, _, _) (v1', _, _) _ =
  error "invToAsm called with non-address arguments"

-- | Return all invariant methods in given context
collectInvariants :: Addr -> Context -> [Method]
collectInvariants addr ctx =
  filter (\mtd -> mtd ^. L.methodKind == Invariant) . M.elems $ ctx ^. L.ctxObjs .
  ix addr .
  L.objMethods

-- | Return all non-relational proof obligations generated by invariants
invToVCnonRelational :: [Prop] -> Addr -> Result -> Verify [VC]
invToVCnonRelational assms addr res@(v, ctx, pathCond) = do
  let univInvs = collectInvariants addr ctx
  fmap concat . forM univInvs $ \univInv -> do
    let formals = univInv ^. L.methodFormals
    (args, ctx', pathCond') <- E.symArgs ctx formals
    let scope = M.fromList (zip (map fst formals) (zip args (map snd formals)))
    paths <-
      symEval
        ( univInv ^. L.methodBody
        , set L.ctxThis addr (set L.ctxScope scope ctx')
        , pathCond' ++ pathCond)
    foreachM (return $ paths) $ \(res, ctxI, pathCondI) ->
      return $
      [ VC
          { _assumptions = nub $ pathCondI ++ assms
          , _conditionName = "univInvPreserved_" ++ (univInv ^. L.methodName)
          , _goal = Not (res :=: VInt 0)
          }
      ]

onlySimpleTypes :: Data p => p -> Verify ()
onlySimpleTypes foo =
  when
    (not . null . listify isNamed $ foo)
    (error $ "Symbolic objects as method arguments not yet supported")
  where
    isNamed :: Type -> Bool
    isNamed (TNamed _) = True
    isNamed _ = False

-- | Return a list of all reference values occurring in some data
collectRefs :: Data p => p -> [Value]
collectRefs = listify isRef
  where
    isRef (VRef _) = True
    isRef _ = False

-- | Substitute x by v in p
substSymVar :: Var -> Value -> Prop -> Prop
substSymVar x v p = everywhereBut (mkQ False binds) (mkT replace) p
  where
    binds (Forall vs e) = x `elem` map fst vs
    binds _ = False
    replace (Sym (SymVar y t))
      | x == y = v
    replace e = e

-- To make Z3 cope with forall quantifications better, make sure there are no forall-quantified
-- variables x occurring in one assumption of the form (x = E) by replacing x by E in the
-- rest of the formula.
onePointTransform ::
     [(Var, Type)] -> [Prop] -> Prop -> ([(Var, Type)], [Prop], Prop)
onePointTransform vs assms conseq =
  foldr removeVar (vs, assms, conseq) spuriousAssms
  where
    spuriousAssms =
      catMaybes $
      map
        (\x ->
           listToMaybe . catMaybes $
           map
             (\assm ->
                case assm of
                  Sym (SymVar y t) :=: e ->
                    if y == x
                      then Just (x, e, assm)
                      else Nothing
                  e :=: Sym (SymVar y t) ->
                    if y == x
                      then Just (x, e, assm)
                      else Nothing
                  _ -> Nothing)
             assms)
        (map fst vs)
    removeVar (spurVar, spurExpr, origAssm) (vs', assms', conseq') =
      ( filter ((/= spurVar) . fst) vs'
      , map (substSymVar spurVar spurExpr) . filter (/= origAssm) $ assms'
      , substSymVar spurVar spurExpr conseq')

universalInvariantAssms :: Addr -> Context -> PathCond -> Verify [Prop]
universalInvariantAssms addr ctx pathCond =
  fmap concat . forM (collectInvariants addr ctx) $ \invariantMethod -> do
    let formals = invariantMethod ^. L.methodFormals
    onlySimpleTypes formals
    (args, ctx', pathCond') <- E.symArgs ctx formals
    let scope = M.fromList (zip (map fst formals) (zip args (map snd formals)))
    let oldRefs = collectRefs ctx'
    let oldSymVars = collectSymVars ctx'
    paths <-
      symEval
        ( invariantMethod ^. L.methodBody
        , set L.ctxThis addr (set L.ctxScope scope ctx)
        , pathCond' ++ pathCond)
    let argNames = map (\(Sym (SymVar name t)) -> (name, t)) args
    foreachM (return paths) $ \(res, ctxI, pathCondI)
      -- If there were symbolic objects created on demand, we may now have a bunch
      -- of extra symbolic variables that were introduced. Since these are going
      -- to be arbitrary parameters, we have to quantify over them as well here:
      -- TODO: check for duplicate symvars of different types
     -> do
      let newSymVars = collectSymVars (res, ctxI, pathCondI) \\ oldSymVars
      let newRefs =
            map (\(VRef a) -> a) $ collectRefs (res, ctxI, pathCondI) \\ oldRefs
      refVars <- mapM (E.freshVar . ("symref" ++) . show) newRefs
      let replaceRef :: Data p => Addr -> Value -> p -> p
          replaceRef a v = everywhere (mkT replace)
            where
              replace (VRef a')
                | a == a' = v
                | otherwise = VRef a'
              replace x = x
          replaceAllRefs :: Data p => p -> p
          replaceAllRefs x =
            foldr
              (\(ref, symref) p -> replaceRef ref symref p)
              x
              (zip newRefs (map (Sym . SymRef) refVars))
          (vs, assms, conseq) =
            onePointTransform
              (nub $ argNames ++ map ((, TInt)) refVars ++ newSymVars)
              pathCondI
              (Not (res :=: VInt 0))
      return $ replaceAllRefs [Forall vs (L.conjunction assms :=>: conseq)]

-- | Type synonym for building up bijections between addresses
type AddrBijection = M.Map Addr Addr

maybeInsert ::
     (Show k, Show v, Ord k, Eq k, Eq v)
  => k
  -> v
  -> M.Map k v
  -> Maybe (M.Map k v)
maybeInsert k v m
  | Just v' <- M.lookup k m =
    if v == v'
      then Just m
      else Nothing
  | otherwise =
    case M.keys $ M.filterWithKey (\k' v' -> v' == v) m of
      ks'
        | not (all (== k) ks') -> Nothing
      _ -> Just (M.insert k v m)

tryInsert ::
     (Show k, Show v, Ord k, Eq k, Eq v) => k -> v -> M.Map k v -> M.Map k v
tryInsert k v m =
  case maybeInsert k v m of
    Just m' -> m'
    Nothing -> error $ "Key " ++ show k ++ " already remapped in " ++ show m

-- | Try to find a mapping for addresses that may make the two values equal.
unifyAddrs :: Value -> Value -> AddrBijection -> AddrBijection
unifyAddrs (VInt i1) (VInt i2) bij = bij
unifyAddrs (VMap vs1) (VMap vs2) bij =
  foldr
    (\(v1, v2) bij' -> unifyAddrs v1 v2 bij')
    bij
    (M.elems $
     M.merge
       M.dropMissing
       M.dropMissing
       (M.zipWithMatched (\k v1 v2 -> (v1, v2)))
       vs1
       vs2)
unifyAddrs (VTuple vs1) (VTuple vs2) bij =
  foldr (\(v1, v2) bij' -> unifyAddrs v1 v2 bij') bij (zip vs1 vs2)
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
    foldM
      (\bij' (v1, v2) -> unifyAddrsExact v1 v2 bij')
      bij
      (M.elems $
       M.merge
         M.dropMissing
         M.dropMissing
         (M.zipWithMatched (\k v1 v2 -> (v1, v2)))
         vs1
         vs2)
unifyAddrsExact (VTuple vs1) (VTuple vs2) bij
  | length vs1 == length vs2 =
    foldM (\bij' (v1, v2) -> unifyAddrsExact v1 v2 bij') bij (zip vs1 vs2)
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
  | length valssL == length valssR
  , and (zipWith ((==) `on` length) valssL valssR) =
    foldM
      (\bij' (valsL, valsR) ->
         foldM
           (\bij'' (valL, valR) -> unifyAddrsExact valL valR bij'')
           bij'
           (zip valsL valsR))
      bij
      (zip valssL valssR)
  | otherwise = Nothing
unifyAddrsExactSym (ITE condL thnL elsL) (ITE condR thnR elsR) bij =
  unifyAddrsExactProp condL condR bij >>= unifyAddrsExact thnL thnR >>=
  unifyAddrsExact elsL elsR
unifyAddrsExactSym (Z vL) (Z vR) bij = unifyAddrsExact vL vR bij
unifyAddrsExactSym (Call funL argsL) (Call funR argsR) bij
  | funL == funR && length argsL == length argsR =
    foldM
      (\bij' (argL, argR) -> unifyAddrsExact argL argR bij')
      bij
      (zip argsL argsR)
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

allAddrs :: Data p => p -> [Addr]
allAddrs = nub . map fromRef . listify isAddr
  where
    isAddr (Ref a) = True
    isAddr _ = False
    fromRef (Ref a) = a
    fromRef x = error "fromRef called with non-Ref argument"

-- | Try to find a bijection between addresses to be applied to the right-hand
-- side to make both sides possible to be proven equal. This is a best-effort
-- process and may not return a mapping that actually makes them equal, and may
-- not be complete.
findAddressBijection :: AddrBijection -> Result -> Result -> AddrBijection
findAddressBijection inMap (v, ctx, pathCond) (v', ctx', pathCond') =
  let baseMap = unifyAddrs v v' inMap
      remainingLHSRefs = allAddrs (v, pathCond) \\ M.elems baseMap
      remainingRHSRefs = allAddrs (v', pathCond') \\ M.keys baseMap
   in extendMap baseMap remainingRHSRefs remainingLHSRefs
  where
    extendMap base [] addrPool = base
    extendMap base (a:as) (p:ps)
      | a >= 0 = tryInsert a a (extendMap base as (p : ps))
    extendMap base (a:as) (p:ps) = tryInsert a p (extendMap base as ps)
    extendMap base (a:as) [] =
      let base' = (extendMap base as [])
       in tryInsert a (nextFreeAddr base') base'
    nextFreeAddr m
      | null (M.elems m) = 100
      | otherwise = maximum (M.elems m) + 1

-- | Remap all addresses in a piece of data with given bijection.
applyAddressBijection :: Data p => AddrBijection -> p -> p
applyAddressBijection addrMap = everywhere (mkT replaceAddress)
  where
    replaceAddress :: SymValue -> SymValue
    replaceAddress (Ref addr)
      | addr >= 0 = Ref addr -- new RHS addresses are always negative
      | Just newAddr <- M.lookup addr addrMap = Ref newAddr
      | otherwise = Ref addr -- error $ "No mapping for address: " ++ show addr ++ " in " ++ show addrMap
    replaceAddress v = v

findContradictingBijection :: PathCond -> PathCond -> Maybe AddrBijection
findContradictingBijection [] pcR = Nothing
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
    propR:pcR' -> findContradictingBijection (propL : pcL') pcR'

fallback :: Maybe a -> a -> a
fallback (Just x) y = x
fallback Nothing y = y

-- | Generate the verification conditions for two sets of results (i.e.
-- configurations returned by evaluating a method call with symbolic arguments
-- in a havoced context). Also takes the old havoced environments as arguments
-- to turn invariants into assumptions.
resultsToVCs ::
     [ProofHint] -> Result -> Results -> Result -> Results -> Verify [VC]
resultsToVCs invs old@(VRef addr1, ctxH, pathCondH) ress1 old'@(VRef addr1', ctxH', pathCondH') ress1' = do
  invAssms <-
    (++) <$> universalInvariantAssms addr1 ctxH pathCondH <*>
    universalInvariantAssms addr1' ctxH' pathCondH'
  assms <- (invAssms ++) . concat <$> mapM (invToAsm old old') invs
  -- Invariant methods aren't relational and hence we don't need to check them for each pair of
  -- of paths:
  lhsInvVCs <- foreachM (return ress1) $ invToVCnonRelational assms addr1
  rhsInvVCs <- foreachM (return ress1') $ invToVCnonRelational assms addr1'
  relationalVCs <-
    foreachM (return ress1) $ \res1@(v1, ctx1, pc1) ->
      foreachM (return ress1') $ \res1'@(v1', ctx1', pc1')
        -- if we are able to find a trivial bijection resulting in a
        -- a trivial contradiction in the path conditions, then we are done:
       -> do
        let negRefs = filter (< 0) $ allAddrs (v1', pc1')
        let baseMap =
              case catMaybes $
                   map
                     (\hint ->
                        case hint of
                          UseAddressBijection m -> Just m
                          _ -> Nothing)
                     invs of
                [m] -> trace ("Using user-supplied address map: " ++ show m) $ m
                [] -> M.empty
                _ -> error "More than one address bijection hint"
        let addrMap =
              findContradictingBijection pc1 pc1' `fallback`
              findAddressBijection baseMap res1 res1'
            applyBij :: Data p => p -> p
            applyBij =
              if NoAddressBijection `inPartial` invs
                then id
                else applyAddressBijection addrMap
        -- Note that it's fine to only use the address bijection for relational proof
        -- obligations, since non-relational VCs should can not depend on concrete addresses
        -- that the allocator chose.
        -- when (not . null . allAddrs $ v1') $
        let vcRes =
              VC
                { _assumptions = applyBij $ nub $ assms ++ pc1 ++ pc1'
                , _conditionName = "resultsEq"
                , _goal = id (v1 :=: applyBij v1')
                }
        invVCs <-
          if ctx1 == ctxH && ctx1' == ctxH'
            then return []
            else concat <$>
                 mapM
                   (fmap applyBij . invToVC assms addr1 res1 addr1' res1')
                   invs
        -- Require that adversary was called with same values:
        let vcAdv =
              VC
                { _assumptions = applyBij $ nub $ assms ++ pc1 ++ pc1'
                , _conditionName = "advCallsEq"
                , _goal =
                    Sym (AdversaryCall (ctx1 ^. L.ctxAdvCalls)) :=:
                    applyBij (Sym (AdversaryCall (ctx1' ^. L.ctxAdvCalls)))
                }
        return $ vcRes : vcAdv : invVCs
  return $ relationalVCs ++ lhsInvVCs ++ rhsInvVCs
resultsToVCs invs (v1, _, _) _ (v1', _, _) _ =
  error $ "resultsToVCs called with non-address values" ++ show (v1, v1')

inPartial :: PartialEq a => a -> [a] -> Bool
inPartial x ys = any ((== Just True) . (=== x)) ys

-- | Collect non-trivial verification conditions for a given method, invariants and arguments
methodEquivalenceVCs ::
     Method -> [ProofHint] -> [Value] -> Result -> Result -> Verify [VC]
methodEquivalenceVCs mtd invs args (VRef a1, ctx1, pathCond1) (VRef a1', ctx1', pathCond1') = do
  ctxH1 <- havocContext ctx1
  ctxH1' <- havocContext ctx1'
  results <-
    symEval
      ( ECall (EConst (VRef a1)) (mtd ^. L.methodName) (map EConst args)
      , ctxH1
      , pathCond1)
  results' <-
    symEval
      ( ECall (EConst (VRef a1')) (mtd ^. L.methodName) (map EConst args)
      , if NoAddressBijection `inPartial` invs
          then ctxH1'
          else set L.ctxAllocStrategy L.Decrease ctxH1'
      , pathCond1')
  vcs <-
    resultsToVCs
      invs
      (VRef a1, ctxH1, pathCond1)
      results
      (VRef a1', ctxH1', pathCond1')
      results'
  filterM
    (\vc -> do
       trivial <- triviallyTrue vc
       if trivial
         then do
           return False
         else return True)
    vcs
methodEquivalenceVCs mtd invs args (v1, _, _) (v1', _, _) =
  error $ "methodEquivalenceVCs called with non-reference values: " ++
  show (v1, v1')

-- | Helper function for writing equality invariants. Produces an exception
-- if the chain of fields doesn't exist in the given context.
getField :: [Var] -> Addr -> Context -> Value
getField [] _ _ = error "Empty list of fields"
getField [x] addr ctx
  | Just v <- ctx ^? L.ctxObjs . ix addr . L.objLocals . ix x . L.localValue = v
  | otherwise = error $ "getField: No such field: " ++ x
getField (x:xs) addr ctx
  | Just (VRef addr') <-
     ctx ^? L.ctxObjs . ix addr . L.objLocals . ix x . L.localValue =
    getField xs addr' ctx
  | otherwise = error $ "Non-reference in field lookup"

-- | Find the shared methods between two objects in their respective contexts
sharedMethods :: Addr -> Context -> Addr -> Context -> [Method]
sharedMethods addrL ctxL addrR ctxR
  | Just objL <- ctxL ^? L.ctxObjs . ix addrL
  , Just objR <- ctxR ^? L.ctxObjs . ix addrR =
    let mtdsL = objL ^. L.objMethods
        mtdsR = objR ^. L.objMethods
        sharedNames = M.keys mtdsL `intersect` M.keys mtdsR
  -- TODO: check that there are no extraneous methods and that they
  -- take the same number (and type) of arguments
     in filter ((== NormalMethod) . (^. L.methodKind)) .
        map (fromJust . (`M.lookup` mtdsL)) $
        sharedNames
  | otherwise = error "Invalid addresses passed to sharedMethods"

-- TODO: merge with previous implementation
freshEmitterVar :: String -> String -> Emitter String
freshEmitterVar prefix' typ = do
  let prefix = filter (`notElem` "?") prefix'
  last <- use (nextEmitterVar . at prefix)
  case last of
    Just n -> do
      nextEmitterVar . ix prefix %= (+ 1)
      let varName = prefix ++ show n
      usedVars %= ((varName, typ) :)
      return varName
    Nothing -> do
      modify (nextEmitterVar . at prefix ?~ 0)
      freshEmitterVar prefix typ

emit :: SolverCmd -> Emitter ()
emit = tell . (: [])

emitRaw :: String -> Emitter ()
emitRaw = emit . Raw

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

-- | Collect all free symbolic variables occurring in some data
-- Only forall statements are considered as variable binders.
collectSymVars :: Data p => p -> [(Var, Type)]
collectSymVars vc =
  nubBy ((==) `on` fst) . map toTup $
  everythingWithContext [] (++) (mkQ ((,) []) collect `extQ` propBind) vc
  where
    collect (SymVar x t) bound
      | x `notElem` bound = ([SymVar x t], bound)
      | otherwise = ([], bound)
    collect _ bound = ([], bound)
    propBind (Forall formals x) bound = ([], bound ++ map fst formals)
    propBind _ bound = ([], bound)
    toTup (SymVar x t) = (x, t)
    toTup _ = undefined

symVarName :: SymValue -> Var
symVarName (SymVar n t) = n
symVarName x = error "symVarName: Not a SymVar: " ++ show x

concatM = fmap concat . sequence
initialEmitterState prefixCtx =
  EmitterState
    { _nextEmitterVar = M.empty
    , _usedVars = []
    , _varTranslations = M.empty
    , _emitterPrefixCtx = prefixCtx
    }

runEmitter :: MonadIO m => Context -> Emitter a -> m (a, [SolverCmd])
runEmitter prefix action =
  liftIO $ evalRWST (unEmitter action) () (initialEmitterState prefix)

-- | Type class for values that can be converted into Z3 terms/formulas
class ToZ3 a where
  toZ3 :: a -> Emitter String

z3Call :: String -> [String] -> String
z3Call fun args = "(" ++ fun ++ " " ++ intercalate " " args ++ ")"

-- | Return an s-expression of applying the first argument to a list things that
-- can be converted to z3 expressions
z3CallM :: (ToZ3 a) => String -> [a] -> Emitter String
z3CallM fun args = z3Call fun <$> mapM toZ3 args

typeToZ3 :: Type -> Emitter String
typeToZ3 TAny = return "Value"
typeToZ3 TInt = return "Int"
typeToZ3 _ = return "Value"

propToZ3 :: Prop -> Emitter String
propToZ3 PTrue = return "true"
propToZ3 PFalse = return "false"
propToZ3 (Not p) = z3CallM "not" [p]
propToZ3 (x :=: y) = z3CallM "=" [x, y]
propToZ3 (x :=>: y) = z3CallM "=>" [x, y]
propToZ3 (x :&: y) = z3CallM "and" [x, y]
propToZ3 (Forall [] p) = toZ3 p
propToZ3 (Forall formals p) = do
  argNames <-
    mapM (\(x, t) -> (,) <$> (translateVar x =<< typeToZ3 t) <*> pure t) formals
  concatM
    [ pure "(forall ("
    , intercalate " " <$>
      mapM
        (\(n, t) -> do
           typ <- typeToZ3 t
           return $ "(" ++ n ++ " " ++ typ ++ ")")
        argNames
    , pure ") "
    , toZ3 p
    , pure ")"
    ]

instance ToZ3 Prop where
  toZ3 = propToZ3

-- To make life easier for Z3, we keep all the data types involved monomorphic,
-- so we have separate types in Z3 for values, lists of values, and lists of lists of values:
valuesToZ3 :: [Value] -> Emitter String
valuesToZ3 [] = return "nil"
valuesToZ3 (v:vs) = z3Call "cons" <$> sequence [toZ3 v, valuesToZ3 vs]

valuessToZ3 :: [[Value]] -> Emitter String
valuessToZ3 [] = return "nils"
valuessToZ3 (vs:vss) =
  z3Call "conss" <$> sequence [valuesToZ3 vs, valuessToZ3 vss]

valueToZ3 :: Value -> Emitter String
valueToZ3 (VInt i) = return $ z3Call "VInt" [show i]
valueToZ3 (VTuple vs) = z3Call "VTuple" <$> sequence [valuesToZ3 vs]
-- valueToZ3 (VMap map) = freshEmitterVar "map" "Value" -- TODO: map same maps to same variable
valueToZ3 (VMap mp) = do
  elts <-
    foldM
      (\m (k, v) -> z3Call "store" <$> sequence [pure m, toZ3 k, toZ3 v])
      "empty-map"
      (M.toList mp)
  return $ z3Call "VMap" [elts]
valueToZ3 VNil = return "VNil"
valueToZ3 (Sym (Ref addr)) =
  return $ z3Call "vref" [show addr] -- vref is an uninterpreted function instead of a constructor
valueToZ3 (Sym sv) = symValueToZ3 sv
valueToZ3 (VSet vs) =
  z3Call "VSet" <$>
  sequence
    [ foldM
        (\set v -> z3Call "store" <$> sequence [pure set, toZ3 v, pure "true"])
        "empty-set"
        (S.toList vs)
    ]

symValueToZ3 :: SymValue -> Emitter String
symValueToZ3 (SymVar x t) =
  case t of
    TInt -> z3Call "VInt" <$> sequence [translateVar x "Int"]
    _ -> translateVar x "Value"
symValueToZ3 (Insert k v m) = z3CallM "insert" [k, v, m]
symValueToZ3 (Lookup k m) = z3CallM "lookup" [k, m]
symValueToZ3 (AdversaryCall vss) =
  z3Call "adversary" <$> sequence [valuessToZ3 vss]
symValueToZ3 (Proj tup idx) = z3CallM "proj" [tup, idx]
symValueToZ3 (Add v1 v2) = z3CallM "add" [v1, v2]
symValueToZ3 (Sub v1 v2) = z3CallM "sub" [v1, v2]
symValueToZ3 (Mul v1 v2) = z3CallM "mul" [v1, v2]
symValueToZ3 (Div v1 v2) = z3CallM "divi" [v1, v2]
symValueToZ3 (Le v1 v2) = z3CallM "le" [v1, v2]
symValueToZ3 (Lt v1 v2) = z3CallM "lt" [v1, v2]
symValueToZ3 (ITE tst thn els) =
  z3Call "ite" <$> sequence [toZ3 tst, toZ3 thn, toZ3 els]
symValueToZ3 (SymRef name) =
  z3Call "vref" <$> sequence [translateVar name "Int"]
symValueToZ3 (Deref obj name) =
  z3Call "deref" <$> sequence [toZ3 obj, pure ("\"" ++ name ++ "\"")]
symValueToZ3 (Ref a) = z3Call "vref" <$> sequence [toZ3 a]
symValueToZ3 (Z v) = z3CallM "Z" [v]
symValueToZ3 (Call fun args) = z3CallM fun args
symValueToZ3 (SetCompr (Sym (SymVar xV TAny)) x pred)
    -- TODO: emit assumptions and newly introduced variables differently so we can handle
    -- them cleanly when occurring in a negative position
 = do
  setVar <- freshEmitterVar ("setcompr_" ++ x) "(Array Value Bool)"
    -- emit $ "(declare-const " ++ setVar ++ " (Array Value Bool))"
  xCode <- translateVar xV "Value"
  predCode <- toZ3 pred
  emitRaw . unlines $
    [ "(assert (forall ((" ++ xCode ++ " Value))"
    , "  (= (select " ++ setVar ++ " " ++ xCode ++ ")"
    , "      " ++ predCode ++ ")))"
    ]
  return $ z3Call "VSet" [setVar]
symValueToZ3 (SetCompr _ _ _) = freshEmitterVar "setCompr" "Value"
  -- set comprehensions with map not supported in z3 backend
symValueToZ3 (MapCompr x val pred) = do
  mapVar <- freshEmitterVar ("mapcompr_" ++ x) "(Array Value Value)"
  emitRaw $ "(declare-const " ++ mapVar ++ " (Array Value Value))"
  xT <- translateVar x "Value"
  predT <- toZ3 pred
  valT <- toZ3 val
  -- if the predicate is satisfied, we map x to f(x)
  emitRaw . unlines $
    [ "(assert (forall ((" ++ xT ++ " Value))"
    , "  (=> " ++ predT
    , "      (= (select " ++ mapVar ++ " " ++ xT ++ ")"
    , "         " ++ valT ++ "))))"
    ]
  -- otherwise, x is not in the map:
  emitRaw . unlines $
    [ "(assert (forall ((" ++ xT ++ " Value))"
    , "  (=> (not " ++ predT ++ ")"
    , "      (= (select " ++ mapVar ++ " " ++ xT ++ ")"
    , "         (VInt 0)))))"
    ]
  return $ z3Call "VMap" [mapVar]
symValueToZ3 (Union s1 s2) = z3CallM "vunion" [s1, s2]
symValueToZ3 (Intersect s1 s2) = z3CallM "vintersect" [s1, s2]
symValueToZ3 (MapUnion m1 m2) = z3CallM "munion" [m1, m2]
symValueToZ3 (In elt set) = z3CallM "vmember" [elt, set]
symValueToZ3 (Submap v1 v2) = z3CallM "is-submap" [v1, v2]

-- symValueToZ3 x = error $ "symValueToZ3: unhandled value: " ++ show x
instance ToZ3 Integer where
  toZ3 = return . show

-- | Runs an action in a writer monad, but suppresses its output and instead
-- returns it in the results
intercept :: MonadWriter w m => m a -> m (a, w)
intercept action = censor (const mempty) (listen action)

vcToZ3 :: VC -> Emitter ()
vcToZ3 vc
  -- Emit declarations for uninterpreted functions:
 = do
  decls <- use (emitterPrefixCtx . L.ctxFunDecls)
  forM decls $ \decl -> do
    emitRaw
      (z3Call
         "declare-fun"
         [ decl ^. L.funDeclName
         , "(" ++
           intercalate " " (replicate (length (decl ^. L.funDeclArgs)) "Value") ++
           ")"
         , "Value"
         ])
    -- FIXME: For debugging the envelope encryption proof, we emit an assumption that skenc never fails to encrypt
    -- to do this properly, we'd allow specifying such assumptions in the surface syntax
    when (decl ^. L.funDeclName == "skenc") $
      emitRaw
        (z3Call
           "assert"
           [ z3Call
               "forall"
               [ "(" ++
                 intercalate
                   " "
                   (map
                      (\arg -> "(" ++ arg ++ " Value)")
                      (decl ^. L.funDeclArgs)) ++
                 ")"
               , z3Call
                   "not"
                   [ z3Call
                       "="
                       [ z3Call (decl ^. L.funDeclName) (decl ^. L.funDeclArgs)
                       , "(VInt 0)"
                       ]
                   ]
               ]
           ])
  emitRaw $ ";; " ++ (vc ^. conditionName)
  -- FIXME: this is a hacky way to make sure we output the variable
  -- declarations before the places where we need them.
  -- Really we should be doing this in a more structured way.
  (translatedAssms, assmOutput) <- intercept $ mapM toZ3 (vc ^. assumptions)
  (goalProp, goalOutput) <- intercept $ toZ3 (vc ^. goal)
  vars <- use usedVars
  forM vars $ \(var, typ) -> emitRaw $ z3Call "declare-const" [var, typ]
  mapM_ emit (assmOutput ++ goalOutput)
  mapM_ (\asm -> emitRaw (z3Call "assert" [asm])) translatedAssms
  emitRaw $ z3Call "assert" [z3Call "not" [goalProp]]

sendToZ3 :: String -> Verify ()
sendToZ3 line = do
  (hin, _, _) <- use E.z3Proc
  liftIO $ hPutStrLn hin line

readLineFromZ3 :: Verify String
readLineFromZ3 = do
  (_, hout, _) <- use E.z3Proc
  liftIO $ hGetLine hout

solverCmdToZ3 :: SolverCmd -> String
solverCmdToZ3 (Raw s) = s
solverCmdToZ3 e = "; unimplemented: solverCmdToZ3 (" ++ show e ++ ")"

checkWithZ3 :: VC -> Verify Bool
checkWithZ3 vc = do
  pctx <- use E.verifyPrefixCtx
  -- TODO: implement a more structured way to handle variable
  -- declarations inside a translation function
  (_, vcLines) <-
    fmap (second (nub . map solverCmdToZ3)) . runEmitter pctx $ vcToZ3 vc
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
  pctx <- use E.verifyPrefixCtx
  (_, vcLines) <-
    fmap (second (nub . map solverCmdToZ3)) . runEmitter pctx $ vcToZ3 vc
  tempFile <-
    liftIO $ writeTempFile "." "z3-vc.smt2" $ unlines $ z3Prelude : vcLines ++
    ["(check-sat)"]
  return tempFile

-- | Verify conditions with external solvers and return unverified conditions
checkVCs :: [VC] -> Verify [VC]
checkVCs [] = return []
checkVCs vcs = do
  debug $ show (length vcs) ++ " verification conditions"
  (t, vcs') <- Timer.time $ filterM (fmap not . checkWithZ3) vcs
  when (not . null $ vcs') $ do
    debug $ "Remaining VCs in Z3 files: "
    mapM_ (\vc -> writeToZ3File vc >>= debug) vcs'
  debug $ show (length vcs') ++ " VCs left after checking with Z3 (" ++
    Timer.formatSeconds t ++
    ")"
  return vcs'

checkEqv :: Bool -> Expr -> [ProofHint] -> Expr -> Expr -> Verify [(Var, [VC])]
checkEqv useSolvers prefix hints lhs rhs
  | any ((== Just True) . (=== Admit)) hints = do
      debug $ "Skipping proof step: " ++ show lhs ++ " ~ " ++ show rhs
      return []
checkEqv useSolvers prefix [Rewrite from to] lhs rhs = do
  (_, prefixCtx, _) <- fmap E.singleResult . symEval $ (prefix, L.emptyCtx, [])
  unless
    ((from, to) `elem` (prefixCtx ^. L.ctxAssumptions) || (to, from) `elem`
     (prefixCtx ^. L.ctxAssumptions)) $
    fail $
    "No such assumption: " ++
    show from ++
    " ≈ " ++
    show to
  if lhs' == rhs
    then return []
    else error $ "Invalid rewrite step:\n" ++ show lhs' ++ "\n/=\n" ++ show rhs
  where
    lhs' = rewriteExpr from to lhs
checkEqv useSolvers prefix hintsIn lhs rhs = do
  cached <- S.member (lhs, rhs) <$> use E.alreadyVerified
  (_, hints, _) <- inferInvariants prefix (lhs, hintsIn, rhs)
  withCache <- view E.useCache
  let noteText =
        concatMap
          (\hint ->
             case hint of
               Note n -> n
               _ -> "")
          hints
      note =
        if noteText == ""
          then ""
          else noteText ++ ": "
  if cached && not (any ((== Just True) . (=== IgnoreCache)) hints) && withCache
    then do
      debug $ note ++ "Skipping cached verification step"
      return []
    else do
      (_, prefixCtx, pathCond) <-
        fmap E.singleResult . symEval $ (prefix, L.emptyCtx, [])
      E.verifyPrefixCtx .= prefixCtx
      res1@(VRef a1, ctx1, _) <-
        E.singleResult <$> symEval (lhs, prefixCtx, pathCond)
      res1'@(VRef a1', ctx1', _) <-
        E.singleResult <$> symEval (rhs, prefixCtx, pathCond)
    -- check that invariants hold initially
      invLHS <- invToVCnonRelational [] a1 res1
      invRHS <- invToVCnonRelational [] a1' res1'
      invsRel <- concat <$> mapM (invToVC [] a1 res1 a1' res1') hints
      remainingInvVCs <- checkVCs (invLHS ++ invRHS ++ invsRel)
      let mtds = sharedMethods a1 ctx1 a1' ctx1'
    -- check that there are no other methods except invariants:
      let allMethods :: Addr -> Context -> S.Set String
          allMethods addr ctx =
            S.fromList . map (^. L.methodName) .
            filter ((== NormalMethod) . (^. L.methodKind)) .
            M.elems $
            (ctx ^. L.ctxObjs . ix addr . L.objMethods)
          lhsMethods = allMethods a1 ctx1
          rhsMethods = allMethods a1' ctx1'
      when (lhsMethods /= rhsMethods) $
      -- FIXME: output which methods are the extra ones
       do
        let extraMtds =
              (lhsMethods `S.difference` rhsMethods) `S.union`
              (rhsMethods `S.difference` lhsMethods)
        error $ note ++
          "LHS and RHS do not have the same non-invariant methods; extra methods: " ++
          show extraMtds
      (t, remainingVCs) <-
        fmap (second ([("_invsInit", remainingInvVCs)] ++)) . Timer.time $
        forM mtds $ \mtd -> do
          debug $ note ++ "Checking method: " ++ mtd ^. L.methodName
          onlySimpleTypes (mtd ^. L.methodFormals)
          (args, _, _) <- E.symArgs ctx1 (mtd ^. L.methodFormals)
      -- TODO: double-check that we don't need path condition here.
          vcs <- methodEquivalenceVCs mtd hints args res1 res1'
          verificationResult <-
            if useSolvers
              then checkVCs vcs
              else return vcs
          return (mtd ^. L.methodName, verificationResult)
      if (not . all (null . snd) $ remainingVCs)
        then do
          liftIO . putStrLn $ note ++ "Verification failed for step: "
          liftIO $ print remainingVCs
        else do
          cacheVerified lhs rhs
          liftIO . putStrLn $ note ++ "Verification succeeded in " ++
            Timer.formatSeconds t
      return remainingVCs

-- | Mark a pair of expressions as successfully verified in the cache
cacheVerified :: Expr -> Expr -> Verify ()
cacheVerified lhs rhs = do
  E.alreadyVerified %= S.insert (lhs, rhs)
  verified <- use E.alreadyVerified
  liftIO $ BS.writeFile "cache.bin" (encode verified)

-- | Check two quivela files for equivalence using a list of invariants. The
-- first quivela file contains shared global variables and method definitions
-- (The other two programs are evaluated in the context resulting from
-- evaluating the prefix file). If the first argument is False, external solvers
-- will not be used.
checkEqvFile ::
     Bool
  -> FilePath
  -> [ProofHint]
  -> FilePath
  -> FilePath
  -> Verify [(Var, [VC])]
checkEqvFile verify prefixFile invs lhsFile rhsFile = do
  prefix <- P.parseFile prefixFile
  lhs <- P.parseFile lhsFile
  rhs <- P.parseFile rhsFile
  checkEqv verify prefix invs lhs rhs

-- | Quivela proofs are a series of equivalent expressions and a list of
-- invariants that are needed to verify this step.
type Step = (Expr, [ProofHint], Expr)

-- | Check given list of steps and return a list of unverified VCs for each step
checkSteps :: Expr -> [Step] -> Verify [[(Var, [VC])]]
checkSteps prefix =
  mapM (\(lhs, invs, rhs) -> checkEqv True prefix invs lhs rhs)

-- | @'rewriteExpr' from to e@ rewrites all occurrences of @from@ in @e@ by @to@
-- TODO: take bound variables into account
rewriteExpr :: Expr -> Expr -> Expr -> Expr
rewriteExpr from to e = everywhere (mkT replace) e
  where
    replace :: Expr -> Expr
    replace e'
      | e' == from = to
      | otherwise = e'

-- | Convenience function for expression that both sides agree on looking
-- up a series of fields. @[a, b, c]@ represents looking up field @a.b.c@.
fieldsEqual :: [Var] -> [Var] -> ProofHint
fieldsEqual fieldsL fieldsR = EqualInv (getField fieldsL) (getField fieldsR)

-- | Like 'fieldsEqual' but looking up the same fields on both sides.
fieldEqual :: [Var] -> ProofHint
fieldEqual fields = fieldsEqual fields fields

-- | Clears the proof cache
clearCache :: IO ()
clearCache = do
  exists <- doesFileExist "cache.bin"
  when exists $ removeFile "cache.bin"

commonVars :: [Var] -> Addr -> Context -> Addr -> Context -> [[Var]]
commonVars prefixFields addrL ctxL addrR ctxR
  | Just objL <- ctxL ^. L.ctxObjs . at addrL
  , Just objR <- ctxR ^. L.ctxObjs . at addrR =
    let common =
          M.filterWithKey
            (\field locL ->
               case objR ^. L.objLocals . at field of
                 Just locR ->
                   locL ^. L.localType == locR ^. L.localType &&
                   not (locL ^. L.localImmutable) &&
                   not (locR ^. L.localImmutable) &&
                   locL ^.
                   L.localValue ==
                   locR ^.
                   L.localValue
                 _ -> False)
            (objL ^. L.objLocals)
        commonObjs =
          M.mapWithKey
            (\field locL ->
               case ( locL ^. L.localValue
                    , objR ^? L.objLocals . ix field . L.localValue) of
                 (VRef aL, Just (VRef aR)) -> Just (field, aL, aR)
                 _ -> Nothing)
            (objL ^. L.objLocals)
     in map (\field -> prefixFields ++ [field]) (M.keys common) ++
        (concatMap
           (\(field, aL, aR) ->
              commonVars (prefixFields ++ [field]) aL ctxL aR ctxR) .
         catMaybes .
         M.elems $
         commonObjs)
  | otherwise = error "commonVars called with invalid addresses"

inferInvariants :: Expr -> Step -> Verify Step
inferInvariants prefix step@(lhs, invs, rhs)
  | any (\x -> (x === NoInfer) == Just True) invs = return step
  | otherwise = do
    (_, prefixCtx, _) <- E.singleResult <$> symEval (prefix, L.emptyCtx, [])
    (VRef addrL, ctxL, _) <- E.singleResult <$> symEval (lhs, prefixCtx, [])
    (VRef addrR, ctxR, _) <- E.singleResult <$> symEval (rhs, prefixCtx, [])
    let comVars = commonVars [] addrL ctxL addrR ctxR
    debug $ "Inferred equality invariants on fields: " ++ show comVars
    return (lhs, invs ++ map fieldEqual comVars, rhs)

-- | Convert a series of proof parts into a sequence of steps
toSteps :: [ProofPart] -> [Step]
toSteps [] = []
toSteps [_] = []
toSteps (Prog lhs:PDiff diffs:steps') =
  toSteps (Prog lhs : Prog (applyDiffs diffs lhs) : steps')
toSteps (Prog lhs:Hint h:PDiff diffs:steps') =
  toSteps (Prog lhs : Hint h : Prog (applyDiffs diffs lhs) : steps')
toSteps (Prog lhs:Prog rhs:steps') =
  (lhs, [], rhs) : toSteps (Prog rhs : steps')
toSteps (Prog lhs:Hint invs:Prog rhs:steps') =
  (lhs, invs, rhs) : toSteps (Prog rhs : steps')
toSteps _ = error "Invalid sequence of steps"

proveStep :: Expr -> Step -> Verify Int
proveStep prefix (lhs, invs, rhs) = do
  remaining <- checkEqv True prefix invs lhs rhs
  return . sum . map (length . snd) $ remaining

-- | A handy alias for cons; this makes a sequence of proof steps look more like
-- an actual equivalence relation.
(~~) :: a -> [a] -> [a]
x ~~ y = x : y

infixr 5 ~~

-- | Like '~~' but using a nicer-looking unicode operator instead.
(≈) :: a -> [a] -> [a]
x ≈ y = x : y

infixr 5 ≈
