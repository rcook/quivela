module Quivela.Parse (parseExpr, parseFile) where

import Control.Applicative ((<$>))
import Control.Arrow (second)
import Control.Monad
import Control.Lens hiding (Context(..))
import Control.Lens.At
import Control.Monad.List
import Control.Monad.IO.Class
import Control.Monad.RWS.Strict
import Data.List
import Data.Data
import Data.Generics
import Data.Maybe
import Data.Typeable
import qualified Data.Map as M
import qualified Data.Set as S
import qualified ErrM as P
import qualified AbsQuivela as P
import qualified LexQuivela as P
import qualified ParQuivela as P

import Quivela.SymEval

-- The normalize* functions that an expression as returned by the BNFC grammar
-- and return a more compact AST as used by the symbolic evaluator. In the long
-- run we should write a parser that produces this directly instead.

normalizeAST :: P.Expr -> Expr
normalizeAST e =
  case e of
    P.EAssign lhs rhs -> EAssign (normalizeAST lhs) (normalizeAST rhs)
    P.EProj obj (P.Id name) ->
      EProj (normalizeAST obj) name
    P.EIdx base idx -> EIdx (normalizeAST base) (normalizeAST idx)
    P.ECall (P.EVar (P.Id name)) args ->
      ECall (EConst VNil) name (map normalizeAST args)
    P.ECall (P.EProj obj (P.Id name)) args ->
      ECall (normalizeAST obj) name (map normalizeAST args)
    P.EVar (P.Id name) -> EVar name
    P.EConst val -> EConst (normalizeVal val)
    P.ETuple exprs -> ETuple (map normalizeAST exprs)
    P.ETupleProj e1 e2 ->
      ETupleProj (normalizeAST e1) (normalizeAST e2)
    P.EMethod (P.Id name) args body ->
      EMethod name (map normalizeArg args) (normalizeAST body)
    P.ENew fields body ->
      ENew (map normalizeField fields) (normalizeAST body)
    P.EAmp e1 e2 ->
      ECall (EConst VNil) "&" [normalizeAST e1, normalizeAST e2]
    P.EOr e1 e2 ->
      ECall (EConst VNil) "|" [normalizeAST e1, normalizeAST e2]
    P.EEq e1 e2 ->
      ECall (EConst VNil) "==" [normalizeAST e1, normalizeAST e2]
    P.ENot e ->
      ECall (EConst VNil) "!" [normalizeAST e]
    P.EAdd e1 e2 ->
      ECall (EConst VNil) "+" (map normalizeAST [e1, e2])
    P.ESub e1 e2 ->
      ECall (EConst VNil) "-" (map normalizeAST [e1, e2])
    P.EMul e1 e2 ->
      ECall (EConst VNil) "*" (map normalizeAST [e1, e2])
    P.EDiv e1 e2 ->
      ECall (EConst VNil) "/" (map normalizeAST [e1, e2])
    P.EPostIncr e ->
      ECall (EConst VNil) "++" [normalizeAST e]
    P.ELt e1 e2 ->
      ECall (EConst VNil) "<" [normalizeAST e1, normalizeAST e2]
    P.ESeq e1 e2 ->
      ESeq (normalizeAST e1) (normalizeAST e2)
    _ -> error $ "[normalizeAST] Unhandled case: " ++ show e

normalizeVal :: P.Val -> Value
normalizeVal (P.VInt i) = VInt i
normalizeVal (P.VMap) = VMap M.empty

normalizeArg :: P.Arg -> (Var, Type)
normalizeArg (P.UArg (P.Id name)) = (name, TAny)
normalizeArg (P.TArg (P.Id name) typ) = (name, normalizeType typ)

normalizeType :: P.Type -> Type
normalizeType P.TInt = TInt
normalizeType P.TAny = TAny
normalizeType (P.TTuple ts) = TTuple (map normalizeType ts)
normalizeType (P.TMap tk tv) = TMap (normalizeType tk) (normalizeType tv)
normalizeType (P.TNamed (P.Id name)) = TNamed name

normalizeField :: P.Init -> Field
normalizeField (P.UInit mod (P.Id name) e) =
  Field { _fieldName = name, _fieldInit = normalizeAST e
        , _fieldType = TAny, _immutable = mod == P.ConstMod }
normalizeField (P.TInit mod (P.Id name) t e) =
  Field { _fieldName = name, _fieldInit = normalizeAST e
        , _fieldType = normalizeType t, _immutable = mod == P.ConstMod }

parseExpr :: String -> Expr
parseExpr s =
  case P.pExpr (P.myLexer s) of
    P.Ok pexpr -> normalizeAST pexpr
    P.Bad err -> error $ "Parse error: " ++ err

parseFile :: MonadIO m => FilePath -> m Expr
parseFile f = parseExpr <$> liftIO (readFile f)
