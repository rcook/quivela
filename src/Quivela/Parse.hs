-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.Parse
  ( parseExpr
  , parseFile
  , parseProofPart
  ) where

import qualified Control.Lens as C
import Control.Lens ((^.), set)
import qualified Control.Monad.IO.Class as MC
import Data.Function (on)
import Data.List (nubBy)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Text.Parsec as P
import Text.Parsec (Parsec, (<?>), (<|>), eof, sepBy, try)
import qualified Text.Parsec.Expr as E
import Text.Parsec.Expr
  ( Assoc(AssocLeft, AssocNone, AssocRight)
  , Operator(Infix, Postfix, Prefix)
  )
import Text.Parsec.Language (emptyDef)
import qualified Text.Parsec.Token as Token

import qualified Quivela.Language as L
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

languageDef =
  emptyDef
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

semi = Token.semi lexer -- parses a semicolon

whiteSpace = Token.whiteSpace lexer -- parses whitespace

symbol = Token.symbol lexer

data ParserState = ParserState
  { _inTuple :: Bool
              -- ^ keeps track if we are currently parsing a tuple, in which case
              -- we resolve the ambiguity of > as a closing bracket for the tuple.
              -- Comparisons inside tuples can be written with explicit parentheses
              -- as in <1, (2 > 3)>
  , _inFieldInit :: Bool
  , _inArgs :: Bool
  , _pipeAsOr :: Bool
  } deriving (Eq, Read, Show, Ord)

C.makeLenses ''ParserState

type Parser = Parsec String ParserState

value :: Parser Value
value =
  VInt <$> integer <|> (reserved "map" *> pure (VMap M.empty)) <|>
  try
    (VSet . S.fromList <$>
     (symbol "{" *> withState (set inTuple True) (value `sepBy` symbol ",") <*
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
             (set pipeAsOr True .
              set inArgs False . set inFieldInit False . set inTuple False)
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
  base <- withState (set inTuple True) expr
  pred <-
    (symbol "," *> withState (set inTuple True) expr) <|> pure (EConst (VInt 1))
  return (name, base, pred)

assumeExpr :: Parser Expr
assumeExpr = reserved "assume" *> (EAssume <$> expr <*> (symbol "≈" *> expr))

setComprExpr :: Parser Expr
setComprExpr = do
  symbol "{"
  fun <- withState (set pipeAsOr False) expr
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
  val <- withState (set inTuple True . set pipeAsOr False) expr
  symbol "|"
  pred <- withState (set inTuple True) expr
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
  elts <- withState (set inTuple True) $ expr `sepBy` symbol ","
  symbol ">"
  return $ ETuple elts

baseExpr :: Parser Expr
baseExpr =
  EVar <$> identifier <|> EConst <$> value <|>
  tuple <?> "number, variable, or tuple"

projExpr :: Parser Expr
projExpr = EProj <$> baseExpr <*> (symbol "." *> identifier)

projExpr' :: Expr -> Parser Expr
projExpr' expr = EProj expr <$> (symbol "." *> identifier)

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
        else pure ""
      return e

unqualifiedFunCall :: Parser Expr
unqualifiedFunCall =
  ECall (EConst VNil) <$> identifier <*>
  callParams <?> "unqualified function call"

callParams :: Parser [Expr]
callParams =
  (symbol "(" *> withState (set inArgs True) (expr `sepBy` symbol ",") <*
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
  id <- identifier
  typ <- try (symbol ":" *> typ) <|> pure TAny
  init <- try (symbol "=" *> expr) <|> pure (EVar id)
  return $
    Field
      { _fieldName = id
      , _fieldInit = init
      , _fieldType = typ
      , _immutable = isConst
      }

-- | Fails if list elements are not unique under given function; returns its argument unchanged otherwise
uniqueBy :: (Show a, Eq b) => (a -> b) -> [a] -> Parser [a]
uniqueBy f lst
  | length (nubBy ((==) `on` f) lst) == length lst = return lst
  | otherwise = fail $ "List elements not unique: " ++ show lst

uniqueFields :: [Field] -> Parser [Field]
uniqueFields = uniqueBy (^. L.fieldName)

newExpr :: Parser Expr
newExpr =
  ENew <$>
  (reserved "new" *> symbol "(" *>
   withState (set inFieldInit True) (uniqueFields =<< field `sepBy` symbol ",") <*
   symbol ")") <*>
  (symbol "{" *> (foldr ESeq ENop <$> P.many expr) <* symbol "}") <?>
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
     (set inFieldInit True)
     ((uniqueBy fst =<< constrArg `sepBy` symbol ",") <?>
      "constructor keyword arguments") <*
   symbol ")")

methodArg :: Parser (String, Type)
methodArg =
  (do id <- identifier
      typ <- try (symbol ":" *> typ) <|> pure TAny
      return (id, typ)) <?>
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
  if fld ^. L.fieldInit == EVar (fld ^. L.fieldName)
        -- the field parser defaults to the field's name if no initialization expression is given
    then return
           ( (fld ^. L.fieldName, fld ^. L.immutable, fld ^. L.fieldType) : args
           , values)
    else case fld ^. L.fieldInit of
           EConst v -> return (args, (fld ^. L.fieldName, v) : values)
           e ->
             fail $
             "Non-constant field initialization in type declaration: " ++ show e

typedecl :: Parser Expr
typedecl = do
  reserved "type"
  typeName <- identifier
  symbol "=" *> reserved "new"
  fields <-
    symbol "(" *> withState (set inFieldInit True) (field `sepBy` symbol ",") <*
    symbol ")"
  body <- symbol "{" *> (foldr ESeq ENop <$> P.many expr) <* symbol "}"
  (formals, values) <- splitTypeDeclFields fields
  let result =
        ETypeDecl
          { _typedeclName = typeName
          , _typedeclFormals = formals
          , _typedeclValues = values
          , _typedeclBody = body
          }
  let freeVars = fst . L.varBindings $ result
  -- Maybe move this check out of the parser to somewhere else:
  if S.null freeVars
    then return result
    else fail $ "Free variables in type declaration: " ++ show freeVars

functionDecl :: Parser Expr
functionDecl =
  reserved "function" *>
  (EFunDecl <$> identifier <*>
   (symbol "(" *> identifier `sepBy` symbol "," <* symbol ")"))

program :: Parser Expr
program = foldr1 ESeq <$> P.many1 expr

overrideMethod :: Parser L.Diff
overrideMethod = OverrideMethod <$> methodExpr

deleteMethod :: Parser Diff
deleteMethod = DeleteMethod <$> (reserved "delete" *> identifier)

diffs :: Parser [Diff]
diffs = P.many1 methodDiff

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

diffOrProg :: Parser L.ProofPart
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
    Right expr -> expr

parseExpr :: String -> Expr
parseExpr s = parse program s

parseFile :: MC.MonadIO m => FilePath -> m Expr
parseFile file = parseExpr <$> MC.liftIO (readFile file)

parseProofPart :: String -> L.ProofPart
parseProofPart = parse diffOrProg
