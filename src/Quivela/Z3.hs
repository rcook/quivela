{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-} -- Readability of the DSL below requires us to disable this
{-# OPTIONS_GHC -Wno-missing-monadfail-instances #-} -- Readability of the DSL below requires us to disable this

module Quivela.Z3
  ( prelude
  , renderCommands
  , vcToSmt
  ) where

import Control.Arrow (first)
import Control.Lens ((^.))
import Control.Monad (liftM2, liftM3, unless)
import qualified Control.Monad.State as State
import Control.Monad.State (State, get, modify)
import qualified Data.List as L
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Quivela.Language as Q
import Quivela.Language (Prop((:&:), (:=:), (:=>:)))
import Quivela.Prelude
import qualified SMTLib2 as S
import SMTLib2 (Expr, Ident(I), Name(N))
import qualified SMTLib2.Array as S
import SMTLib2.Array (tArray)
import qualified SMTLib2.Core as S
import SMTLib2.Core ((===), (==>), tBool)
import qualified SMTLib2.Int as S
import SMTLib2.Int (tInt)
import Text.PrettyPrint as PP

-- ----------------------------------------------------------------------------
-- SMT-LIB builtins
-- ----------------------------------------------------------------------------
type Fun = [Expr] -> Expr

constExpr :: S.Type -> Fun
constExpr = S.App (I (N "const") []) . Just

and, or :: Name
and = N "and"

or = N "or"

baseType :: String -> S.Type
baseType t = S.TApp (I (N t) []) []

tString :: S.Type
tString = baseType "String"

i :: String -> S.Ident
i x = I (N x) []

e :: String -> Expr
e c = S.app (i c) []

forall1 :: (String, S.Type) -> Expr -> Expr
forall1 (x, t) = S.Quant S.Forall [S.Bind (N x) t]

forall2 :: (String, S.Type) -> (String, S.Type) -> Expr -> Expr
forall2 (x1, t1) (x2, t2) =
  S.Quant S.Forall [S.Bind (N x1) t1, S.Bind (N x2) t2]

-- Z3 has a generic mapping function, syntax ((_ map f) a b c)
-- for a method f of arity 3.  This is a hack to get
-- around the lack of generic (E1 E2) syntax in SMTLIB, used
-- by Z3
amap :: Name -> [Expr] -> Expr
amap f = S.app . i . oneline . S.pp $ S.app (i "_") [e "map", S.app (I f []) []]
  where
    oneline = PP.renderStyle (PP.style {PP.lineLength = 10000000})

tuple2 :: ([a] -> a) -> (a -> a -> a)
tuple2 f x y = f [x, y]

tuple3 :: ([a] -> a) -> (a -> a -> a -> a)
tuple3 f x y z = f [x, y, z]

renderCommands :: [S.Command] -> String
renderCommands = PP.render . PP.vcat . map S.pp

nzero :: Expr
nzero = S.num (0 :: Int)

pat :: Expr -> Expr -> Expr
pat exp p = S.Annot exp [S.Attr (N "pattern") (Just p)]

-- ----------------------------------------------------------------------------
-- Translation Monad
-- ----------------------------------------------------------------------------
data S = S
  { _vars :: Map S.Name S.Type
  , _commands :: [S.Command]
  }

type M a = State S a

newCommand :: S.Command -> M ()
newCommand c = modify (\(S vs cs) -> S vs (c : cs))

assert :: Expr -> M ()
assert = newCommand . S.CmdAssert

comment :: String -> M ()
comment = newCommand . S.CmdComment

declareFunWithName :: String -> [S.Type] -> S.Type -> M (Name, Fun)
declareFunWithName f ts t =
  let n = N f
   in do newCommand $ S.CmdDeclareFun n ts t
         return (n, S.app $ i f)

declareFun :: String -> [S.Type] -> S.Type -> M Fun
declareFun f ts t = snd <$> declareFunWithName f ts t

defineFunWithName ::
     String -> [(String, S.Type)] -> S.Type -> Expr -> M (Name, Fun)
defineFunWithName f ts t exp =
  let n = N f
   in do newCommand $
           S.CmdDefineFun n (map (\(x, typ) -> S.Bind (N x) typ) ts) t exp
         return (n, S.app $ i f)

defineFun :: String -> [(String, S.Type)] -> S.Type -> Expr -> M Fun
defineFun f ts t exp = snd <$> defineFunWithName f ts t exp

-- Since types can be recursive, we need a little fixedpoint just for
-- the type components
declareDatatype ::
     String
  -> (S.Type -> [(String, [(String, S.Type)])])
  -> M (S.Type, [(Fun, [Fun])])
declareDatatype t f =
  let n = N t
      typ = S.TApp (I n []) []
      cons = f typ
      cmd =
        S.CmdDeclareDatatype n [] $
        map (\(con, args) -> (N con, map (first N) args)) cons
      funs =
        map
          (\(con, args) -> (S.app (i con), map (\(g, _) -> S.app (i g)) args))
          cons
   in do newCommand cmd
         return (typ, funs)

-- Since types can be recursive, we need a little fixedpoint just for
-- the type components
declareDatatypes ::
     [String]
  -> ([S.Type] -> [[(String, [(String, S.Type)])]])
  -> M ([S.Type], [[(Fun, [Fun])]])
declareDatatypes ts f =
  let ns = map N ts
      typs = map (\n -> S.TApp (I n []) []) ns
      conss = f typs
      cmd =
        S.CmdDeclareDatatypes (map (, 0) ns) $
        map
          (\cons -> ([], map (\(con, args) -> (N con, map (first N) args)) cons))
          conss
      funs =
        map
          (map (\(c, args) -> (S.app (i c), map (\(g, _) -> S.app (i g)) args)))
          conss
   in do newCommand cmd
         return (typs, funs)

setOption :: String -> Bool -> M ()
setOption k v =
  newCommand $
  S.CmdSetOption
    (S.OptAttr $
     S.Attr
       (N k)
       (Just $
        if v
          then S.true
          else S.false))

prelude' :: M (Q.Context -> Q.VC -> M (), [S.Command])
prelude' = do
  comment
    "Disable automatic self configuration in favor of pattern/trigger-based instantiation"
  setOption "smt.auto-config" False
  setOption "smt.mbqi" False -- "Disable automatic self configuration in favor of pattern/trigger-based instantiation."
  comment "Datatypes"
  ([tValue, tValues], [[(vint, [_val]), (vnil, []), (vset, [_valset]), (vmap, [_valmap]), (vtuple, [_elts])], [(nil, []), (cons, [_hd, _tl])]]) <-
    declareDatatypes ["Value", "Values"] $ \[tValue, tValues] ->
      [ [ ("VInt", [("val", tInt)])
        , ("VNil", [])
        , ("VSet", [("valSet", tArray tValue tBool)])
        , ("VMap", [("valMap", tArray tValue tValue)])
        , ("VTuple", [("elts", tValues)])
        ]
      , [("nil", []), ("cons", [("hd", tValue), ("tl", tValues)])]
      ]
  (tValuess, [(nils, []), (conss, [_hds, _tls])]) <-
    declareDatatype "Valuess" $ \tValuess ->
      [("nils", []), ("conss", [("hds", tValues), ("tls", tValuess)])]
  let vnum :: Integer -> Expr
      vnum = vint . pure . S.num
      vzero = vnum 0
      vone = vnum 1
      tArrayVB = tArray tValue tBool
      tArrayVV = tArray tValue tValue
  deref <- declareFun "deref" [tValue, tString] tValue
  comment
    "Trying to access any field on the empty message (0) always results in 0"
  assert . forall1 ("s", tString) $ deref [vzero, e "s"] === vzero
  comment "Address/Value coercions"
  vref <- declareFun "vref" [tInt] tValue
  vrefInv <- declareFun "vref-inv" [tValue] tInt
  assert . forall1 ("a", tInt) $
    pat (vrefInv [vref [e "a"]] === e "a") (vref [e "a"])
  comment "new never returns the 0 bitstring"
  assert . forall1 ("a", tInt) $ S.not (vref [e "a"] === vzero)
  comment "Maps"
  emptyMap <- defineFun "empty-map" [] tArrayVV $ constExpr tArrayVV [vzero]
  toMap <- declareFun "to-map" [tValue] tArrayVV
  assert $ toMap [vzero] === emptyMap []
  assert . forall1 ("m", tArrayVV) $ toMap [vmap [e "m"]] === e "m"
  insert <-
    defineFun "insert" [("k", tValue), ("v", tValue), ("m", tValue)] tValue $
    vmap [S.store (toMap [e "m"]) (e "k") (e "v")]
  lookup <-
    defineFun "lookup" [("k", tValue), ("m", tValue)] tValue $
    S.select (toMap [e "m"]) (e "k")
  (combineDeclName, combineDecl) <-
    declareFunWithName "combine-decl" [tValue, tValue] tValue
  combine <-
    defineFun "combine" [("v", tValue), ("w", tValue)] tValue $
    S.ite (vzero === e "v") (e "w") (e "v")
  assert . forall2 ("v", tValue) ("w", tValue) $
    combineDecl [e "v", e "w"] === combine [e "v", e "w"]
  munion <-
    defineFun "munion" [("k", tValue), ("v", tValue)] tValue $
    vmap [amap combineDeclName [toMap [e "k"], toMap [e "v"]]]
  isSubmapInternal <-
    defineFun "is-submap-internal" [("m1", tArrayVV), ("m2", tArrayVV)] tBool $
    forall1 ("k", tValue) $
    (S.select (e "m2") (e "k") === vzero) ==>
    (S.select (e "m1") (e "k") === vzero)
  isSubmap <-
    defineFun "is-submap" [("v", tValue), ("w", tValue)] tValue $
    S.ite (isSubmapInternal [toMap [e "v"], toMap [e "w"]]) vone vzero
  comment "Int arithmetic"
  toInt <- declareFun "to-int" [tValue] tInt
  assert . forall1 ("n", tInt) $ toInt [vint [e "n"]] === e "n"
  add <-
    defineFun "add" [("v", tValue), ("w", tValue)] tValue $
    vint [S.nAdd (toInt [e "v"]) (toInt [e "w"])]
  sub <-
    defineFun "sub" [("v", tValue), ("w", tValue)] tValue $
    vint [S.nSub (toInt [e "v"]) (toInt [e "w"])]
  mul <-
    defineFun "mul" [("v", tValue), ("w", tValue)] tValue $
    vint [S.nMul (toInt [e "v"]) (toInt [e "w"])]
  divi <-
    defineFun "divi" [("v", tValue), ("w", tValue)] tValue $
    vint [S.nDiv (toInt [e "v"]) (toInt [e "w"])]
  lt <-
    defineFun "lt" [("v", tValue), ("w", tValue)] tValue $
    S.ite (S.nLt (toInt [e "v"]) (toInt [e "w"])) vone vzero
  le <-
    defineFun "le" [("v", tValue), ("w", tValue)] tValue $
    S.ite (S.nLeq (toInt [e "v"]) (toInt [e "w"])) vone vzero
  adversary <- declareFun "adversary" [tValuess] tValue
  zeros <- declareFun "zeros" [tInt] tValue
  length <- declareFun "length" [tValue] tInt
  assert . forall1 ("n", tInt) $ length [zeros [e "n"]] === e "n"
  assert $ length [vzero] === nzero
  assert . forall1 ("v", tValue) $ S.nGeq (length [e "v"]) nzero
  assert . forall1 ("v", tValue) $
    S.not (e "v" === vzero) ==> S.nGt (length [e "v"]) nzero
  assert . forall2 ("a", tInt) ("b", tInt) $
    length [vref [e "a"]] === length [vref [e "b"]]
  z <- defineFun "Z" [("v", tValue)] tValue $ zeros [length [e "v"]]
  comment "Tuples"
  proj <- declareFun "proj" [tValue, tValue] tValue
  comment "Sets"
  toSet <- declareFun "to-set" [tValue] tArrayVB
  emptySet <- defineFun "empty-set" [] tArrayVB $ constExpr tArrayVB [S.false]
  assert $ toSet [vzero] === emptySet []
  assert . forall1 ("set", tArrayVB) $
    pat (toSet [vset [e "set"]] === e "set") (vset [e "set"])
  vunion <-
    defineFun "vunion" [("v", tValue), ("w", tValue)] tValue $
    vset [amap or [toSet [e "v"], toSet [e "w"]]]
  vmember <-
    defineFun "vmember" [("v", tValue), ("w", tValue)] tValue $
    S.ite (S.select (toSet [e "w"]) (e "v")) vone vzero
  vintersect <-
    defineFun "vintersect" [("v", tValue), ("w", tValue)] tValue $
    vset [amap and [toSet [e "v"], toSet [e "w"]]]
  let typ :: Q.Type -> S.Type
      typ Q.TInt = S.tInt
      typ _ = tValue
      prop :: Prop -> M Expr
      prop Q.PTrue = return S.true
      prop Q.PFalse = return S.false
      prop (Q.Not p) = S.not <$> prop p
      prop (x :=: y) = liftM2 (===) (value x) (value y)
      prop (x :=>: y) = liftM2 (==>) (prop x) (prop y)
      prop (x :&: y) = liftM2 S.and (prop x) (prop y)
      prop (Q.Forall [] p) = prop p
      prop (Q.Forall xs p) =
        S.Quant S.Forall (map (\(x, t) -> S.Bind (N x) (typ t)) xs) <$> prop p
      values :: [Q.Value] -> M Expr
      values [] = return $ nil []
      values (v:vs) = liftM2 (tuple2 cons) (value v) (values vs)
      valuess :: [[Q.Value]] -> M Expr
      valuess [] = return $ nils []
      valuess (vs:vss) = liftM2 (tuple2 conss) (values vs) (valuess vss)
      value :: Q.Value -> M Expr
      value (Q.VInt n) = return $ vnum n
      value (Q.VTuple vs) = vtuple . pure <$> values vs
      value (Q.VMap mp) =
        vmap . pure <$>
        foldM
          (\exp (k, v) ->
             liftM2 (\k' v' -> S.store exp k' v') (value k) (value v))
          (emptyMap [])
          (Map.toList mp)
      value Q.VNil = return $ vnil []
      value (Q.Sym (Q.Ref addr)) = return $ vref [S.num addr] -- vref is an uninterpreted function instead of a constructor
      value (Q.Sym sv) = sym sv
      value (Q.VSet vs) =
        vset . pure <$>
        foldM
          (\exp k -> (\k' -> S.store exp k' S.true) <$> value k)
          (emptySet [])
          (Set.toList vs)
      sym :: Q.SymValue -> M Expr
      sym (Q.SymVar x t) = newVar x (typ t)
      sym (Q.Insert k v m) = op3 insert k v m
      sym (Q.Lookup k m) = op2 lookup k m
      sym (Q.AdversaryCall vss) = op1' valuess adversary vss
      sym (Q.Proj tup idx) = op2 proj tup idx
      sym (Q.Add v1 v2) = op2 add v1 v2
      sym (Q.Sub v1 v2) = op2 sub v1 v2
      sym (Q.Mul v1 v2) = op2 mul v1 v2
      sym (Q.Div v1 v2) = op2 divi v1 v2
      sym (Q.Le v1 v2) = op2 le v1 v2
      sym (Q.Lt v1 v2) = op2 lt v1 v2
      sym (Q.ITE tst thn els) =
        op3'
          prop
          value
          value
          (\[tstE, thnE, elsE] -> S.ite tstE thnE elsE)
          tst
          thn
          els
      sym (Q.SymRef name) = return $ vref [e name]
      sym (Q.Deref obj name) =
        (\obj' -> deref [obj', S.Lit $ S.LitStr name]) <$> value obj
      sym (Q.Ref a) = return $ vref [S.num a]
      sym (Q.Z v) = op1 z v
      sym (Q.Call fun args) = S.app (i fun) <$> mapM value args
      sym (Q.Union s1 s2) = op2 vunion s1 s2
      sym (Q.Intersect s1 s2) = op2 vintersect s1 s2
      sym (Q.MapUnion m1 m2) = op2 munion m1 m2
      sym (Q.In elt s) = op2 vmember elt s
      sym (Q.Submap v1 v2) = op2 isSubmap v1 v2
      sym (Q.MapCompr x v p) = do
        mapVar <- newVar ("mapcompr_" ++ x) tArrayVV
        p' <- prop p
        v' <- value v
        assert . forall1 (x, tValue) $ p' ==> (S.select mapVar (e x) === v')
        assert . forall1 (x, tValue) $
          S.not p' ==> (S.select mapVar (e x) === vnum 0)
        return $ vmap [mapVar]
      -- FIXME: Set comprehensions are a mess
      sym (Q.SetCompr x (Q.Sym (Q.SymVar xV Q.TAny)) p) = do
        p' <- prop p
        setVar <- newVar ("setcompr_" ++ x) tArrayVB
        assert . forall1 (xV, tValue) $ S.select setVar (e xV) === p'
        return $ vset [setVar]
      sym (Q.SetCompr _ _ _) = newVar "setCompr" tValue
      newVar :: String -> S.Type -> M Expr
      newVar x t = do
        modify (\(S vs cs) -> S (Map.insertWithKey f (N x) t vs) cs)
        return $
          if t == S.tInt
            then vint [e x]
            else e x
        where
          f (N k) t1 t2
            | t1 == t2 = t1
            | otherwise =
              error $
              printf
                "Variable %s defined at types %s and %s"
                k
                (show t1)
                (show t2)
      op1' :: (a -> M Expr) -> Fun -> a -> M Expr
      op1' f1 f v1 = f . pure <$> f1 v1
      op1 :: Fun -> Q.Value -> M Expr
      op1 = op1' value
      op2 :: Fun -> Q.Value -> Q.Value -> M Expr
      op2 op v1 v2 = liftM2 (tuple2 op) (value v1) (value v2)
      op3' ::
           (a -> M Expr)
        -> (b -> M Expr)
        -> (c -> M Expr)
        -> Fun
        -> a
        -> b
        -> c
        -> M Expr
      op3' f1 f2 f3 f v1 v2 v3 = liftM3 (tuple3 f) (f1 v1) (f2 v2) (f3 v3)
      op3 :: Fun -> Q.Value -> Q.Value -> Q.Value -> M Expr
      op3 = op3' value value value
      vcf :: Q.Context -> Q.VC -> M ()
      vcf ctx (Q.VC name assms goal) = do
        mapM_
          (\(Q.FunDecl f args) ->
             newCommand $
             S.CmdDeclareFun (N f) (L.map (const tValue) args) tValue)
          (Map.elems (ctx ^. Q.ctxFunDecls))
        comment name
        mapM_ (\a -> prop a >>= assert) assms
        prop goal >>= \g -> assert (S.not g)
  S v cs <- get
  unless (Map.null v) (error "nonempty vars in prelude")
  return (vcf, cs)

prelude :: [S.Command]
vc :: Q.Context -> Q.VC -> M ()
(vc, prelude) =
  let (prop, cmds) = State.evalState prelude' (S Map.empty [])
   in (prop, L.reverse cmds)

vcToSmt :: Q.Context -> Q.VC -> [S.Command]
vcToSmt ctx cond =
  let S vars cmds = State.execState (vc ctx cond) (S Map.empty [])
      decls = map (uncurry S.CmdDeclareConst) (L.sort $ Map.toList vars)
   in decls ++ (L.reverse cmds) ++ [S.CmdCheckSat]
