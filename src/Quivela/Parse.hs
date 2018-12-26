-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-} -- Parser has lots of intermediate parsers with complex types

module Quivela.Parse
  ( parseExpr
  , parseFile
  , parseProofPart
  ) where

import Control.Applicative ((<*>), (<*), (*>))
import qualified Control.Lens as Lens
import Control.Lens ((^.))
import qualified Control.Monad as Monad
import qualified Control.Monad.IO.Class as MonadIO
import Control.Monad.IO.Class(MonadIO)
import qualified Data.Function as F
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Quivela.Language as Q
import Quivela.Language
  ( Diff(..)
  , Expr(..)
  , Field(..)
  , MethodKind(..)
  , ProofPart(..)
  , Type(..)
  , Value(..)
  , Var
  )
import Quivela.Prelude
import qualified System.IO as IO
import qualified Text.Parsec as P
import Text.Parsec (Parsec, (<?>), (<|>), eof, sepBy, try)
import qualified Text.Parsec.Expr as E
import Text.Parsec.Expr
  ( Assoc(AssocLeft, AssocNone, AssocRight)
  , Operator(Infix, Postfix, Prefix)
  )
import qualified Text.Parsec.Language as Language
import qualified Text.Parsec.Token as Token

languageDef =
  Language.emptyDef
    { Token.commentStart = "/*"
    , Token.commentEnd = "*/"
    , Token.commentLine = "//"
    , Token.identStart = P.letter <|> P.char '_'
    , Token.identLetter = P.alphaNum <|> P.char '_'
    , Token.reservedNames =
        [ "if"
        , "then"
        , "else"
        , "new"
        , "invariant"
        , "local"
        , "method"
        , "type"
        , "map"
        , "delete"
        , "in"
        , "set"
        , "function"
        , "assume"
        ]
    , Token.reservedOpNames =
        [ "+"
        , "-"
        , "*"
        , "/"
        , "="
        , "<"
        , "<="
        , "&"
        , "|"
        , "!"
        , "."
        , "["
        , "]"
        , "^"
        , "∈"
        , "⊆"
        ]
    }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier

reserved = Token.reserved lexer -- parses a reserved name

reservedOp = Token.reservedOp lexer -- parses an operator

parens = Token.parens lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them

integer = Token.integer lexer -- parses an integer

whiteSpace = Token.whiteSpace lexer -- parses whitespace

symbol s = do
  _ <- Token.symbol lexer s
  return ()

data ParserState = ParserState
  { _inTuple :: Bool
              -- ^ keeps track if we are currently parsing a tuple, in which case
              -- we resolve the ambiguity of > as a closing bracket for the tuple.
              -- Comparisons inside tuples can be written with explicit parentheses
              -- as in <1, (2 > 3)>
  , _inFieldInit :: Bool
  , _inArgs :: Bool
  , _pipeAsOr :: Bool
  } deriving (Eq, Ord, Show)

Lens.makeLenses ''ParserState

type Parser = Parsec String ParserState

value :: Parser Value
value =
  VInt <$> integer <|> (reserved "map" *> pure (VMap M.empty)) <|>
  try
    (VSet . S.fromList <$>
     (symbol "{" *> withState (Lens.set inTuple True) (value `sepBy` symbol ",") <*
      symbol "}"))

binCall :: String -> Expr -> Expr -> Expr
binCall fun e1 e2 = ECall (EConst VNil) fun [e1, e2]

withState :: (u -> u) -> Parsec s u a -> Parsec s u a
withState f action = do
  oldState <- P.getState
  P.modifyState f
  res <- action
  P.putState oldState
  return res

expr :: Parser Expr
expr = do
  inTup <- (^. inTuple) <$> P.getState
  inField <- (^. inFieldInit) <$> P.getState
  inArg <- (^. inArgs) <$> P.getState
  pipeOr <- (^. pipeAsOr) <$> P.getState
  let table =
        [ [prefix "!" (ECall (EConst VNil) "!" . (: []))]
        , [postfix "++" (ECall (EConst VNil) "++" . (: []))]
        , [binary "`" ETupleProj AssocLeft]
        , [binary "∈" EIn AssocNone, binary "⊆" ESubmap AssocNone]
        , [ binary "*" (binCall "*") AssocLeft
          , binary "/" (binCall "/") AssocLeft
          ]
        , [ binary "+" (binCall "+") AssocLeft
          , binary "-" (binCall "-") AssocLeft
          ]
        , [ binary "<" (binCall "<") AssocNone
          , binary "==" (binCall "==") AssocNone
          , binary "<=" (binCall "<=") AssocNone
          ] ++
          (if inTup
             then []
             else [binary ">" (binCall ">") AssocNone])
        , [binary "=" EAssign AssocNone]
        , [binary "&" (binCall "&") AssocRight] ++
          (if pipeOr
             then [binary "|" (binCall "|") AssocRight]
             else []) ++
          (if inField || inTup || inArg
             then []
             else [binary "," ESeq AssocRight])
        ]
  E.buildExpressionParser table term
  where
    term = do
      base <-
        parens
          (withState
             (Lens.set pipeAsOr True .
              Lens.set inArgs False . Lens.set inFieldInit False . Lens.set inTuple False)
             expr) <|>
        try unqualifiedFunCall <|>
        try baseExpr <|>
        ifExpr <|>
        try setComprExpr <|>
        try mapComprExpr <|>
        try newExpr <|>
        try newConstrExpr <|>
        methodExpr <|>
        typedecl <|>
        assumeExpr <|>
        functionDecl <?> "basic expression"
      try (combExpr base) <|> return base
    binary name fun assoc =
      Infix
        (do reservedOp name
            return fun)
        assoc
    prefix name fun =
      Prefix
        (do reservedOp name
            return fun)
    postfix name fun =
      Postfix
        (do reservedOp name
            return fun)

comprSuffix :: Parser (Var, Expr, Expr)
comprSuffix = do
  symbol "|"
  name <- identifier
  (reserved "in" <|> (symbol "∈" *> pure ()))
  -- TODO: rename inTuple, inArgs, etc. to something like "commaAsSeq"
  base <- withState (Lens.set inTuple True) expr
  pred <-
    (symbol "," *> withState (Lens.set inTuple True) expr) <|> pure (EConst (VInt 1))
  return (name, base, pred)

assumeExpr :: Parser Expr
assumeExpr = reserved "assume" *> (EAssume <$> expr <*> (symbol "≈" *> expr))

setComprExpr :: Parser Expr
setComprExpr = do
  symbol "{"
  fun <- withState (Lens.set pipeAsOr False) expr
  (name, base, pred) <- comprSuffix
  symbol "}"
  return $
    ESetCompr
      { _comprVar = name
      , _comprPred = ECall (EConst VNil) "&" [EIn (EVar name) base, pred]
      , _comprValue = fun
      }

-- TODO: Why is map comprehension syntax/functionality so different from set comprehensions?
mapComprExpr :: Parser Expr
mapComprExpr = do
  symbol "["
  var <- identifier
  symbol "->" <|> symbol "↦"
  val <- withState (Lens.set inTuple True . Lens.set pipeAsOr False) expr
  symbol "|"
  pred <- withState (Lens.set inTuple True) expr
  symbol "]"
  return $ EMapCompr {_comprPred = pred, _comprValue = val, _comprVar = var}

combExpr :: Expr -> Parser Expr
combExpr prefix = do
  next <-
    try (ECall prefix <$> (symbol "." *> identifier) <*> callParams) <|>
    try (EIdx prefix <$> (symbol "[" *> expr <* symbol "]")) <|>
    try (EProj prefix <$> (symbol "." *> identifier)) <|>
    pure ENop
  if next == ENop
    then return prefix
    else combExpr next

tuple :: Parser Expr
tuple = do
  symbol "<"
  elts <- withState (Lens.set inTuple True) $ expr `sepBy` symbol ","
  symbol ">"
  return $ ETuple elts

baseExpr :: Parser Expr
baseExpr =
  EVar <$> identifier <|> EConst <$> value <|>
  tuple <?> "number, variable, or tuple"

ifExpr :: Parser Expr
ifExpr =
  EIf <$> (reserved "if" *> symbol "(" *> expr <* symbol ")") <*> ifArm <*>
  (reserved "else" *> ifArm) <?> "conditional"
  where
    ifArm = do
      inBraces <- (symbol "{" *> pure True) <|> pure False
      e <- expr
      if inBraces
        then symbol "}"
        else pure ()
      return e

unqualifiedFunCall :: Parser Expr
unqualifiedFunCall =
  ECall (EConst VNil) <$> identifier <*>
  callParams <?> "unqualified function call"

callParams :: Parser [Expr]
callParams =
  (symbol "(" *> withState (Lens.set inArgs True) (expr `sepBy` symbol ",") <*
   symbol ")") <?>
  "method call arguments"

typ :: Parser Type
typ =
  (reserved "int" *> pure TInt) <|> (symbol "*" *> pure TAny) <|>
  (TTuple <$> (symbol "<" *> typ `sepBy` symbol "," <* symbol ">")) <|>
  (TMap <$> (reserved "map" *> typ) <*> typ) <|>
  (TNamed <$> identifier) <?> "type"

field :: Parser Field
field = do
  isConst <- try (reserved "const" *> pure True) <|> pure False
  x <- identifier
  ty <- try (symbol ":" *> typ) <|> pure TAny
  init <- try (symbol "=" *> expr) <|> pure (EVar x)
  return $
    Field
      { _fieldName = x
      , _fieldInit = init
      , _fieldType = ty
      , _immutable = isConst
      }

-- | Fails if list elements are not unique under given function; returns its argument unchanged otherwise
uniqueBy :: (Show a, Eq b) => (a -> b) -> [a] -> Parser [a]
uniqueBy f lst
  | L.length (L.nubBy ((==) `F.on` f) lst) == L.length lst = return lst
  | otherwise = Monad.fail $ "List elements not unique: " ++ show lst

uniqueFields :: [Field] -> Parser [Field]
uniqueFields = uniqueBy (^. Q.fieldName)

newExpr :: Parser Expr
newExpr =
  ENew <$>
  (reserved "new" *> symbol "(" *>
   withState (Lens.set inFieldInit True) (field `sepBy` symbol "," >>= uniqueFields) <*
   symbol ")") <*>
  (symbol "{" *> (L.foldr ESeq ENop <$> P.many expr) <* symbol "}") <?>
  "new(){} expression"

constrArg :: Parser (Var, Expr)
constrArg =
  (,) <$> (identifier <?> "constructor parameter name") <*>
  (symbol "=" *> expr) <?> "constructor argument (x = e)"

newConstrExpr :: Parser Expr
newConstrExpr =
  ENewConstr <$> (reserved "new" *> identifier) <*>
  (symbol "(" *>
   withState
     (Lens.set inFieldInit True)
     ((constrArg `sepBy` symbol "," >>= uniqueBy fst) <?>
      "constructor keyword arguments") <*
   symbol ")")

methodArg :: Parser (String, Type)
methodArg =
  (do x <- identifier
      ty <- try (symbol ":" *> typ) <|> pure TAny
      return (x, ty)) <?>
  "method argument"

methodExpr :: Parser Expr
methodExpr =
  (do kind <-
        (reserved "method" *> pure NormalMethod) <|>
        (reserved "invariant" *> pure Invariant) <|>
        (reserved "local" *> pure LocalMethod)
      EMethod <$> identifier <*>
        (symbol "(" *> methodArg `sepBy` symbol "," <* symbol ")") <*>
        (symbol "{" *> expr <* symbol "}") <*>
        pure kind) <?>
  "method definition"

-- | Split field declarations into formal parameters for type declarations
-- and constant field initializations. Fails if there is a non-constant
-- initialization. This function is only monadic in order to report
-- such invalid fields as a parse error.
splitTypeDeclFields :: [Field] -> Parser ([(Var, Bool, Type)], [(Var, Value)])
splitTypeDeclFields [] = return ([], [])
splitTypeDeclFields (fld:flds) = do
  (args, values) <- splitTypeDeclFields flds
  if fld ^. Q.fieldInit == EVar (fld ^. Q.fieldName)
        -- the field parser defaults to the field's name if no initialization expression is given
    then return
           ( (fld ^. Q.fieldName, fld ^. Q.immutable, fld ^. Q.fieldType) : args
           , values)
    else case fld ^. Q.fieldInit of
           EConst v -> return (args, (fld ^. Q.fieldName, v) : values)
           e ->
             Monad.fail $
             "Non-constant field initialization in type declaration: " ++ show e

typedecl :: Parser Expr
typedecl = do
  reserved "type"
  typeName <- identifier
  symbol "=" *> reserved "new"
  fields <-
    symbol "(" *> withState (Lens.set inFieldInit True) (field `sepBy` symbol ",") <*
    symbol ")"
  body <- symbol "{" *> (L.foldr ESeq ENop <$> P.many expr) <* symbol "}"
  (formals, values) <- splitTypeDeclFields fields
  let result =
        ETypeDecl
          { _typedeclName = typeName
          , _typedeclFormals = formals
          , _typedeclValues = values
          , _typedeclBody = body
          }
  let freeVars = fst . Q.varBindings $ result
  -- Maybe move this check out of the parser to somewhere else:
  if S.null freeVars
    then return result
    else Monad.fail $ "Free variables in type declaration: " ++ show freeVars

functionDecl :: Parser Expr
functionDecl =
  reserved "function" *>
  (EFunDecl <$> identifier <*>
   (symbol "(" *> identifier `sepBy` symbol "," <* symbol ")"))

program :: Parser Expr
program = L.foldr1 ESeq <$> P.many1 expr

overrideMethod :: Parser Diff
overrideMethod = OverrideMethod <$> methodExpr

deleteMethod :: Parser Diff
deleteMethod = DeleteMethod <$> (reserved "delete" *> identifier)

methodDiff :: Parser Diff
methodDiff = deleteMethod <|> overrideMethod

modField :: Parser [Diff]
modField = do
  reserved "new" *> symbol "(" *> symbol "..." *> symbol ","
  fieldOp <-
    try (NewField <$> field) <|>
    (reserved "delete" *> (DeleteField <$> identifier))
  symbol ")"
  symbol "{" *> symbol "..."
  rest <- P.many methodDiff
  symbol "}"
  return $ fieldOp : rest

initialParserState :: ParserState
initialParserState =
  ParserState
    {_inTuple = False, _inFieldInit = False, _pipeAsOr = True, _inArgs = False}

diffOrProg :: Parser ProofPart
diffOrProg =
  try ((PDiff <$> modField) <* whiteSpace <* P.lookAhead eof) <|>
  try (PDiff <$> (P.many1 methodDiff <* whiteSpace <* P.lookAhead eof)) <|>
  (Prog <$> program)

parse :: Parser a -> String -> a
parse p s =
  case P.runParser
         (whiteSpace *> p <* whiteSpace <* eof)
         initialParserState
         ""
         s of
    Left err -> error $ "Parse error: " ++ show err
    Right e -> e

parseExpr :: String -> Expr
parseExpr s = parse program s

parseFile :: MonadIO m => FilePath -> m Expr
parseFile file = parseExpr <$> MonadIO.liftIO (IO.readFile file)

parseProofPart :: String -> ProofPart
parseProofPart = parse diffOrProg
