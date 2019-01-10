module Quivela.Z3
  ( vcToSmt
  ) where

import Control.Lens ((^.))
import Control.Monad (liftM2, liftM3)
import qualified Control.Monad.State as State
import Control.Monad.State (State, modify)
import qualified Data.List as L
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Quivela.Language as Q
import Quivela.Language (Prop((:&:), (:=:), (:=>:)))
import Quivela.Prelude
import qualified SMTLib2 as S
import qualified SMTLib2.Array as S
import qualified SMTLib2.Core as S
import SMTLib2.Core ((===), (==>))
import qualified SMTLib2.Int as S
import Text.PrettyPrint as PP

data S = S
  { _vars :: Map S.Name S.Type
  , _commands :: [S.Command]
  }

type M a = State S a

vIdent :: String -> S.Ident
vIdent x = S.I (S.N x) []

vExpr :: String -> S.Expr
vExpr c = S.app (vIdent c) []

app :: String -> [S.Expr] -> S.Expr
app = S.app . vIdent

tValue :: S.Type
tValue = S.TApp (S.I (S.N "Value") []) []

str :: String -> S.Expr
str = S.Lit . S.LitStr

typ :: Q.Type -> S.Type
typ Q.TInt = S.tInt
typ _ = tValue

app' :: String -> [S.Expr] -> M S.Expr
app' s = return . app s

prop :: Q.Prop -> M S.Expr
prop Q.PTrue = return S.true
prop Q.PFalse = return S.false
prop (Q.Not p) = S.not <$> prop p
prop (x :=: y) = liftM2 (===) (value x) (value y)
prop (x :=>: y) = liftM2 (==>) (prop x) (prop y)
prop (x :&: y) = liftM2 S.and (prop x) (prop y)
prop (Q.Forall [] p) = prop p
prop (Q.Forall xs p) =
  S.Quant S.Forall (map (\(x, t) -> S.Bind (S.N x) (typ t)) xs) <$> prop p

values :: [Q.Value] -> M S.Expr
values [] = return $ vExpr "nil"
values (v:vs) = liftM2 (\x y -> app "cons" [x, y]) (value v) (values vs)

values' :: [[Q.Value]] -> M S.Expr
values' [] = return $ vExpr "nils"
values' (vs:vss) = liftM2 (\x y -> app "conss" [x, y]) (values vs) (values' vss)

vnum :: Integer -> S.Expr
vnum = app "VInt" . pure . S.num

value :: Q.Value -> M S.Expr
value (Q.VInt i) = return $ vnum i
value (Q.VTuple vs) = app "VTuple" . pure <$> values vs
value (Q.VMap mp) =
  app "VMap" . pure <$>
  foldM
    (\e (k, v) -> liftM2 (\k' v' -> app "store" [e, k', v']) (value k) (value v))
    (vExpr "empty-map")
    (Map.toList mp)
value Q.VNil = return $ vExpr "VNil"
value (Q.Sym (Q.Ref addr)) = app' "vref" [S.num addr] -- vref is an uninterpreted function instead of a constructor
value (Q.Sym sv) = sym sv
value (Q.VSet vs) =
  app "VSet" . pure <$>
  foldM
    (\e k -> (\k' -> app "store" [e, k', S.true]) <$> value k)
    (vExpr "empty-set")
    (Set.toList vs)

newVar :: String -> S.Type -> M S.Expr
newVar x t = do
  modify (\(S vs cs) -> S (Map.insertWithKey f (S.N x) t vs) cs)
  return $
    if t == S.tInt
      then app "VInt" [x']
      else x'
  where
    f (S.N k) t1 t2
      | t1 == t2 = t1
      | otherwise =
        error $ printf "Variable %s defined at types %s and %s" k (show t1) (show t2)
    x' = vExpr x

newCommand :: S.Command -> M ()
newCommand c = modify (\(S vs cs) -> S vs (c : cs))

assert :: S.Expr -> M ()
assert = newCommand . S.CmdAssert

forall :: String -> S.Expr -> S.Expr
forall x p = S.Quant S.Forall [S.Bind (S.N x) tValue] p

op1' :: (a -> M S.Expr) -> String -> a -> M S.Expr
op1' f1 op v1 = (\v1' -> app op [v1']) <$> f1 v1

op1 :: String -> Q.Value -> M S.Expr
op1 = op1' value

op2 :: String -> Q.Value -> Q.Value -> M S.Expr
op2 op v1 v2 = liftM2 (\v1' v2' -> app op [v1', v2']) (value v1) (value v2)

op3' ::
     (a -> M S.Expr)
  -> (b -> M S.Expr)
  -> (c -> M S.Expr)
  -> String
  -> a
  -> b
  -> c
  -> M S.Expr
op3' f1 f2 f3 op v1 v2 v3 =
  liftM3 (\v1' v2' v3' -> app op [v1', v2', v3']) (f1 v1) (f2 v2) (f3 v3)

op3 :: String -> Q.Value -> Q.Value -> Q.Value -> M S.Expr
op3 = op3' value value value

sym :: Q.SymValue -> M S.Expr
sym (Q.SymVar x t) = newVar x (typ t)
sym (Q.Insert k v m) = op3 "insert" k v m
sym (Q.Lookup k m) = op2 "lookup" k m
sym (Q.AdversaryCall vss) = op1' values' "adversary" vss
sym (Q.Proj tup idx) = op2 "proj" tup idx
sym (Q.Add v1 v2) = op2 "add" v1 v2
sym (Q.Sub v1 v2) = op2 "sub" v1 v2
sym (Q.Mul v1 v2) = op2 "mul" v1 v2
sym (Q.Div v1 v2) = op2 "divi" v1 v2
sym (Q.Le v1 v2) = op2 "le" v1 v2
sym (Q.Lt v1 v2) = op2 "lt" v1 v2
sym (Q.ITE tst thn els) = op3' prop value value "ite" tst thn els
sym (Q.SymRef name) = app' "vref" [vExpr name]
sym (Q.Deref obj name) = (\obj' -> app "deref" [obj', str name]) <$> value obj
sym (Q.Ref a) = app' "vref" [S.num a]
sym (Q.Z v) = op1 "Z" v
sym (Q.Call fun args) = app fun <$> mapM value args
sym (Q.Union s1 s2) = op2 "vunion" s1 s2
sym (Q.Intersect s1 s2) = op2 "vintersect" s1 s2
sym (Q.MapUnion m1 m2) = op2 "munion" m1 m2
sym (Q.In elt s) = op2 "vmember" elt s
sym (Q.Submap v1 v2) = op2 "is-submap" v1 v2
sym (Q.MapCompr x v p) = do
  mapVar <- newVar ("mapcompr_" ++ x) (S.tArray tValue tValue)
  let x' = vExpr x
  p' <- prop p
  v' <- value v
  assert . forall x $ p' ==> (S.select mapVar x' === v')
  assert . forall x $ S.not p' ==> (S.select mapVar x' === vnum 0)
  return $ app "VMap" [mapVar]
-- FIXME: Set comprehensions are a mess
sym (Q.SetCompr (Q.Sym (Q.SymVar xV Q.TAny)) x p) = do
  p' <- prop p
  setVar <- newVar ("setcompr_" ++ x) (S.tArray tValue S.tBool)
  assert . forall xV $ S.select setVar (vExpr xV) === p'
  return $ app "VSet" [setVar]
sym (Q.SetCompr _ _ _) = newVar "setCompr" tValue

vc :: Q.Context -> Q.VC -> M ()
vc ctx (Q.VC name assms goal) = do
  mapM_
    (\(Q.FunDecl f args) ->
       newCommand $ S.CmdDeclareFun (S.N f) (L.map (const tValue) args) tValue)
    (Map.elems (ctx ^. Q.ctxFunDecls))
  newCommand $ S.CmdComment name
  mapM_ (\a -> prop a >>= newCommand . S.CmdAssert) assms
  goal' <- prop goal
  newCommand . S.CmdAssert . S.not $ goal'

vcToSmt :: Q.Context -> Q.VC -> String
vcToSmt ctx cond =
  let S vars cmds = State.execState (vc ctx cond) (S Map.empty [])
      decls = map (\(v, t) -> S.CmdDeclareConst v t) (L.sort $ Map.toList vars)
      commands = decls ++ (L.reverse cmds) ++ [S.CmdCheckSat]
   in PP.render . PP.vcat . map S.pp $ commands
