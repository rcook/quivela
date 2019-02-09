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
  , stepNote
  ) where

import Control.Applicative ((<|>))
import qualified Control.Arrow as Arrow
import qualified Control.Conditional as Cond
import qualified Control.Lens as Lens
import Control.Lens ((%=), (+=), (.=), (^.), (^?))
import qualified Control.Monad.RWS.Strict as Monad
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
import qualified Data.Set.Ordered as OSet
import qualified Data.Text.Prettyprint.Doc as P
import Data.Text.Prettyprint.Doc (pretty)
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
  , PathCtx
  , ProofHint(..)
  , Prop(..)
  , Result
  , SymValue(..)
  , Type(..)
  , VC(..)
  , pattern VRef
  , Value(..)
  , Var
  )
import Quivela.Prelude
import qualified Quivela.Pretty as Doc
import qualified Quivela.SymEval as Q
import Quivela.SymEval (Verify)
import qualified Quivela.Util as Q
import qualified Quivela.Z3 as Q
import qualified System.Directory as Directory
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

-- FIXME: This is just a cleaned up version of the original code.  The lhs is never recursed on.  Can this be correct?
-- FIXME: Eliminate the repeated conversions of PathCond to [Prop].
-- There is probably some really elegant way of expressing this as a
-- fold without the explicit recursion.
findContradictingBijection :: PathCond -> PathCond -> Maybe AddrBijection
findContradictingBijection l r = go (toList l) (toList r)
  where
    go [] _ = Nothing
    go _ [] = Nothing
    go ls@(Not propL:_) (propR:rs) =
      unifyAddrsExactProp propL propR M.empty <|> go ls rs
    go ls@(propL:_) (Not propR:rs) =
      unifyAddrsExactProp propL propR M.empty <|> go ls rs
    go ls (_:rs) = go ls rs

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
stepNote Step {hints = []} = "no-note"
stepNote Step {hints = Note n:_} = n
stepNote s@(Step {hints = _:hs}) = stepNote s {hints = hs}

-- | Return the number of remaining verification conditions
proveStep :: Expr -> Step -> Verify Int
proveStep prefix step = do
  Q.debug $ "---------------------------\nVerifying step: " ++ stepNote step
  remaining <- checkEqv prefix step
  return $ L.sum (map (L.length . snd) remaining)

-- ----------------------------------------------------------------------------
-- Check verification conditions
-- ----------------------------------------------------------------------------
checkEqv :: Expr -> Step -> Verify [(Var, [VC])]
checkEqv _ Step {lhs, hints, rhs}
  | Q.elemPartial Admit hints = do
    Q.debug $ "Skipping proof step: " ++ show (pretty lhs) ++ " ≈ " ++ show (pretty rhs)
    return []
-- Note: We can only rewrite as a single step.  The result must be syntactically
-- identical, so no VCs are generated.
checkEqv prefix Step {lhs, rhs, hints = [Rewrite from to]} = do
  (_, prefixCtx, props) <- fmap Q.singleResult $ Q.symEval (prefix, Q.emptyCtx, mempty)
  Monad.unless (null props) $
    Monad.fail "A non-empty set of propositions was returned"
  let assms = prefixCtx ^. Q.ctxAssumptions
  Monad.unless (L.elem (from, to) assms || L.elem (to, from) assms) $
    Monad.fail ("No such assumption: " ++ show (pretty from) ++ " ≈ " ++ show (pretty to))
  let lhs' = rewriteExpr lhs
  if lhs' == rhs
    then return []
    else error $ "Invalid rewrite step:" ++ show lhs' ++ " = " ++ show rhs
  -- | @'rewriteExpr' from to e@ rewrites all occurrences of @from@ in @e@ by @to@
  -- FIXME: This is unsound.  It must take bound variables into account. Write unit tests for this
  where
    rewriteExpr :: Expr -> Expr
    rewriteExpr e = Generics.everywhere (Generics.mkT replace) e
      where
        replace :: Expr -> Expr
        replace e'
          | e' == from = to
          | otherwise = e'
checkEqv prefix step@Step {lhs, rhs} = do
  cached <- S.member (lhs, rhs) <$> Lens.use Q.alreadyVerified
  step'@Step {hints} <- inferFieldEqualities prefix step
  withCache <- Q.useCache
  let note = stepNote step'
  if withCache && cached && not (Q.elemPartial IgnoreCache hints)
    then do
      Q.debug "Skipping cached verification step"
      return []
    else do
      (_, prefixCtx, _) <-
        Q.singleResult <$> Q.symEval (prefix, Q.emptyCtx, mempty)
      Q.verifyPrefixCtx .= prefixCtx
      -- lhs path condition should be empty
      resL@(VRef aL, ctxL, _) <-
        Q.singleResult <$> Q.symEval (lhs, prefixCtx, mempty)
      -- rhs path condition should be empty
      resR@(VRef aR, ctxR, _) <-
        Q.singleResult <$> Q.symEval (rhs, prefixCtx, mempty)
      -- check that invariants hold initially
      invLHS <- invariantMethodVCs mempty aL ctxL mempty
      invRHS <- invariantMethodVCs mempty aR ctxR mempty
      invsRel <-
        L.concat <$> mapM (invToVC mempty (aL, ctxL, mempty) (aR, ctxR, mempty)) hints
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
          Q.onlySimpleTypes formals
          (args, _, _) <- Q.symArgs ctxL formals
          -- TODO: double-check that we don't need path condition here.
          vcs <- methodEquivalenceVCs mtd hints args resL resR
          verificationResult <- checkVCs vcs
          return (mtd ^. Q.methodName, verificationResult)
      let unfinished = L.filter (not . L.null . snd) remainingVCs
      if L.null unfinished
        then do
          cacheVerified
          Q.debug $ "Verification succeeded in " ++ Timer.formatSeconds t
        else do
          Q.debug . show . P.vcat $ map pretty unfinished
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
    -- | Collect non-trivial verification conditions for a given method, invariants and arguments
    methodEquivalenceVCs ::
         Method -> [ProofHint] -> [Value] -> Result -> Result -> Verify [VC]
    methodEquivalenceVCs mtd invs args (VRef addr1, ctx1, pathCond1) (VRef addr2, ctx2, pathCond2) = do
      ctxH1 <- havocContext ctx1
      ctxH2 <- havocContext ctx2
      let call addr =
            ECall (EConst (VRef addr)) (mtd ^. Q.methodName) (map EConst args)
      results1 <- Q.symEval (call addr1, ctxH1, pathCond1)
      results2 <-
        Q.symEval
          ( call addr2
          , if Q.elemPartial NoAddressBijection invs
              then ctxH2
              else ctxH2 {Q._ctxAllocStrategy = Q.Decrease}
          , pathCond2)
      vcs <-
        do assms <-
             do assms1 <- universalInvariantAssms addr1 ctxH1 pathCond1
                assms2 <- universalInvariantAssms addr2 ctxH2 pathCond2
                assms3 <-
                  mapM
                    (invToAsm
                       (VRef addr1, ctxH1, pathCond1)
                       (VRef addr2, ctxH2, pathCond2))
                    invs
                return $ foldMap OSet.fromListL (assms1 : assms2 : assms3)
           -- Invariant methods aren't relational and hence we don't need to check them for each pair of
           -- of paths:
           lhsInvVCs <-
             Q.foreachM (return results1) $ \(_, c, p) ->
               invariantMethodVCs assms addr1 c p
           rhsInvVCs <-
             Q.foreachM (return results2) $ \(_, c, p) ->
               invariantMethodVCs assms addr2 c p
           relationalVCs <-
             Q.foreachM (return results1) $ \res1@(v1, c1, pc1) ->
               Q.foreachM (return results2) $ \res2@(v2, c2, pc2)
              -- if we are able to find a trivial bijection resulting in a
              -- a trivial contradiction in the path conditions, then we are done:
                -> do
                 let baseMap =
                       case Maybe.catMaybes $
                            map
                              (\case
                                 UseAddressBijection m -> Just m
                                 _ -> Nothing)
                              invs of
                         [m] ->
                           Trace.trace
                             ("Using user-supplied address map: " ++ show m) $
                           m
                         [] -> M.empty
                         _ -> error "More than one address bijection hint"
                 let addrMap =
                       Maybe.fromMaybe
                         (findAddressBijection baseMap res1 res2)
                         (findContradictingBijection pc1 pc2)
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
                         { _assumptions = applyBij $ assms <> pc1 <> pc2
                         , _conditionName = "resultsEq"
                         , _goal = id (v1 :=: applyBij v2)
                         }
                 invVCs <-
                   if c1 == ctxH1 && c2 == ctxH2
                     then return []
                     else L.concat <$>
                          mapM
                            (fmap applyBij .
                             invToVC assms (addr1, c1, pc1) (addr2, c2, pc2))
                            invs
                 -- Require that adversary was called with same values:
                 let vcAdv =
                       VC
                         { _assumptions = applyBij $ assms <> pc1 <> pc2
                         , _conditionName = "advCallsEq"
                         , _goal =
                             Sym (AdversaryCall (c1 ^. Q.ctxAdvCalls)) :=:
                             applyBij
                               (Sym (AdversaryCall (c2 ^. Q.ctxAdvCalls)))
                         }
                 return $ vcRes : vcAdv : invVCs
           return $ relationalVCs ++ lhsInvVCs ++ rhsInvVCs
      Monad.filterM (\vc -> not <$> triviallyTrue vc) vcs
    methodEquivalenceVCs _ _ _ (v1, _, _) (v1', _, _) =
      error $ "methodEquivalenceVCs called with non-reference values: " ++
      show (v1, v1')
    -- | Havoc all objects in a context
    havocContext :: Context -> Verify Context
    havocContext = Generics.everywhereM (Generics.mkM havocObj)
    -- | Havoc all non-immutable locals of an object
    havocObj :: Object -> Verify Object
    havocObj obj
      | obj ^. Q.objAdversary = return obj
      -- ^ this is a hack, since we currently don't support const annotations on global variables
      | otherwise = do
        newLocals <-
          mapM
            (\(name, loc) -> (name, ) <$> havocLocal name loc)
            (M.toList (obj ^. Q.objLocals))
        return (Lens.set Q.objLocals (M.fromList newLocals) obj)
    -- | Havoc a local variable if it's not an immutable variable
    havocLocal :: Var -> Local -> Verify Local
    havocLocal name l
      | not (Lens.view Q.localImmutable l) = do
        fv <- Q.freshVar name
        return $ Lens.set Q.localValue (Sym (SymVar fv (l ^. Q.localType))) l
      | otherwise = return l
    -- | Check if the goal is trivial (equalities like x = x, a goal occurring as an assumption,
    -- and having both P and (not P) as an assumption)
    triviallyTrue :: VC -> Verify Bool
    triviallyTrue vc
      | v1 :=: v1' <- vc ^. Q.goal =
        return $ (v1 == v1') || assumptionsContradictory (vc ^. Q.assumptions)
      | (vc ^. Q.goal) `OSet.member` (vc ^. Q.assumptions) = return True
      | otherwise = return False
    assumptionsContradictory :: PathCond -> Bool
    -- O(N log(N))
    assumptionsContradictory assms =
      L.any
        (\case
           Not p -> p `OSet.member` assms -- O(log(N))
           _ -> False)
        assms -- O(N)

-- | When mutable fields with the same name, type, and value are shared between two
--   expressions in a Step, infer they should be equal.
--   Invariant: input hints are a subset of output hints
inferFieldEqualities :: Expr -> Step -> Verify Step
inferFieldEqualities prefix step@Step {lhs, hints, rhs}
  | Q.elemPartial NoInfer hints = return step
  | L.any Q.isEqualInv hints = return step -- if someone explicitly specifies equalities, don't try to infer others
  | otherwise = do
    (_, prefixCtx, _) <- Q.singleResult <$> Q.symEval (prefix, Q.emptyCtx, mempty)
    (VRef addrL, ctxL, _) <- Q.singleResult <$> Q.symEval (lhs, prefixCtx, mempty)
    (VRef addrR, ctxR, _) <- Q.singleResult <$> Q.symEval (rhs, prefixCtx, mempty)
    if ctxL == ctxR
      then Q.debug $ "Same context: " ++ Doc.show (pretty ctxL)
      else do
        Q.debug $ "Left context: " ++ Doc.show (pretty ctxL)
        Q.debug $ "Right context: " ++ Doc.show (pretty ctxR)
    Q.debug $ "Symbolically evaluated lhs to " ++ Doc.show (pretty addrL)
    Q.debug $ "Symbolically evaluated rhs to " ++ Doc.show (pretty addrR)
    let comVars = commonVars [] addrL ctxL addrR ctxR
    Cond.unless
      (L.null comVars)
      (Q.debug $ "Inferred equality invariants on fields: " ++ ppVars comVars)
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

-- | Verify conditions with external solvers and return unverified conditions
checkVCs :: [VC] -> Verify [VC]
checkVCs [] = return []
checkVCs vcs = do
  Q.debug $ printf "Checking %d verification conditions" (L.length vcs)
  (t, vcs') <- Timer.time $ Monad.filterM (fmap not . checkWithZ3) vcs
  write <- Lens.view Q.writeAllVCsToFile
  let ts = Timer.formatSeconds t
      n = L.length vcs'
  if n == 0
    then Q.debug $ printf "All verification conditions verified (%s)" ts
    else Q.debug $ printf "Can't verify %d verification conditions (%s)" n ts
  -- if write, files are written during the checkWithZ3 step
  Cond.unless write $ mapM_ writeToZ3File vcs'
  return vcs'
  where
    writeToZ3File :: VC -> Verify ()
    writeToZ3File vc = do
      job <- Lens.view Q.jobName
      step <- Lens.view Q.jobStep
      note <- Lens.view Q.jobNote
      tempDir <- Lens.view Q.tempDir
      tmp <-
        Maybe.maybe
          (Monad.liftIO Temp.getCanonicalTemporaryDirectory)
          return
          tempDir
      let dir :: String = printf "%s/quivela/%s/step-%04d-%s" tmp job step note
      Monad.liftIO $ Directory.createDirectoryIfMissing True dir
      pctx <- Lens.use Q.verifyPrefixCtx
      files <- Lens.use Q.tempFiles
      let file :: String = printf "%s/vc-%04d-%s.smt2" dir files (_conditionName vc)
      Q.debug $ printf "Writing %s" file
      Monad.liftIO $ writeFile file (Q.renderCommands $ Q.prelude ++ Q.vcToSmt pctx vc)
      Q.tempFiles += 1
    checkWithZ3 :: VC -> Verify Bool
    checkWithZ3 vc = do
      write <- Lens.view Q.writeAllVCsToFile
      Monad.when write (writeToZ3File vc)
      pctx <- Lens.use Q.verifyPrefixCtx
      sendToZ3 "(push)"
      sendToZ3 (Q.renderCommands $ Q.vcToSmt pctx vc)
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

-- | Compute all relational proof obligations generated by an invariant
invToVC :: PathCond -> PathCtx Addr -> PathCtx Addr -> ProofHint -> Verify [VC]
invToVC assms (addrL, ctxL, pathCondL) (addrR, ctxR, pathCondR) inv =
  case inv of
    EqualInv f g ->
      return
        [ Q.emptyVC
            { _assumptions = pathCondL <> pathCondR <> assms
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
invariantMethodVCs :: PathCond -> Addr -> Context -> PathCond -> Verify [VC]
invariantMethodVCs assms addr ctx pathCond = do
  let univInvs = collectInvariants addr ctx
  fmap L.concat . Monad.forM univInvs $ \univInv -> do
    let formals = univInv ^. Q.methodFormals
    (args, ctx', pathCond') <- Q.symArgs ctx formals
    let scope =
          M.fromList (L.map (\((s, t), v) -> (s, (v, t))) $ L.zip formals args)
    paths <-
      Q.symEval
        ( univInv ^. Q.methodBody
        , ctx' {Q._ctxScope = scope, Q._ctxThis = addr}
        , pathCond' <> pathCond)
    Q.foreachM (return paths) $ \(r, _, c) ->
      return
        [ VC
            { _assumptions = c <> assms
            , _conditionName = "univInvPreserved_" ++ (univInv ^. Q.methodName)
            , _goal = Not (r :=: VInt 0)
            }
        ]

universalInvariantAssms :: Addr -> Context -> PathCond -> Verify [Prop]
universalInvariantAssms addr ctx pathCond =
  fmap L.concat . Monad.forM (collectInvariants addr ctx) $ \invariantMethod -> do
    let formals = invariantMethod ^. Q.methodFormals
    Q.onlySimpleTypes formals
    (args, ctx', pathCond') <- Q.symArgs ctx formals
    let scope =
          M.fromList (L.zip (map fst formals) (L.zip args (map snd formals)))
    let oldRefs = collectRefs ctx'
    let oldSymVars = collectSymVars ctx'
    paths <-
      Q.symEval
        ( invariantMethod ^. Q.methodBody
        , Lens.set Q.ctxThis addr (Lens.set Q.ctxScope scope ctx)
        , pathCond' <> pathCond)
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
      refVars <- mapM (Q.freshVar . ("symref" ++) . show) newRefs
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
         [(Var, Type)] -> PathCond -> Prop -> ([(Var, Type)], PathCond, Prop)
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
                 (toList assms))
            (map fst vs)
        removeVar (spurVar, spurExpr, origAssm) (vs', assms', conseq') =
          ( L.filter ((/= spurVar) . fst) vs'
          , OSet.map (substSymVar spurVar spurExpr) . OSet.filter (/= origAssm) $ assms'
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
