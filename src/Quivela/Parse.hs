{-# LANGUAGE TemplateHaskell #-}
module Quivela.Parse (parseExpr, parseFile, parseProofPart) where

import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import Data.Function
import Data.Maybe
import Data.List
import qualified Data.Set as S
import qualified Data.Map as M
import System.IO
import Text.Parsec hiding (parse)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language

import Quivela.Diff
import Quivela.Language

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter <|> char '_'
           , Token.identLetter     = alphaNum <|> char '_'
           , Token.reservedNames   = [ "if"
                                     , "then"
                                     , "else"
                                     , "new"
                                     , "invariant"
                                     , "method"
                                     , "type"
                                     , "map"
                                     , "delete"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", "="
                                     , "&", "|", "!", ".", "[", "]", "^"
                                     ]
           }

lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace
symbol = Token.symbol lexer

data ParserState =
  ParserState { _inTuple :: Bool
              -- ^ keeps track if we are currently parsing a tuple, in which case
              -- we resolve the ambiguity of > as a closing bracket for the tuple.
              -- Comparisons inside tuples can be written with explicit parentheses
              -- as in <1, (2 > 3)>
              , _inFieldInit :: Bool
              , _inArgs :: Bool
              }
  deriving (Eq, Read, Show, Ord)

makeLenses ''ParserState

type Parser = Parsec String ParserState

value :: Parser Value
value = VInt <$> integer
    <|> (reserved "map" *> pure (VMap M.empty))

binCall :: String -> Expr -> Expr -> Expr
binCall fun e1 e2 = ECall (EConst VNil) fun [e1, e2]

withState :: (u -> u) -> Parsec s u a -> Parsec s u a
withState f action = do
  oldState <- getState
  modifyState f
  res <- action
  putState oldState
  return res

expr :: Parser Expr
expr = do
  inTup <- (^. inTuple) <$> getState
  inField <- (^. inFieldInit) <$> getState
  inArg <- (^. inArgs) <$> getState
  let table =
        [ [ prefix "!" (ECall (EConst VNil) "!" . (:[])) ]
        , [ postfix "++" (ECall (EConst VNil) "++" . (:[])) ]
        , [ binary "`" ETupleProj AssocLeft ]
        , [ binary "*" (binCall "*") AssocLeft, binary "/" (binCall "/") AssocLeft ]
        , [ binary "+" (binCall "+") AssocLeft, binary "-" (binCall "-") AssocLeft ]
        , [ binary "<" (binCall "<") AssocNone
          , binary "==" (binCall "==") AssocNone
          , binary "<=" (binCall "<=") AssocNone ]
          ++ (if inTup then [] else [binary ">" (binCall ">") AssocNone])
        , [ binary "=" EAssign AssocNone ]
        , [ binary "&" (binCall "&") AssocRight
          , binary "|" (binCall "|") AssocRight ]
          ++
          (if inField || inTup || inArg then [] else [binary "," ESeq AssocRight])
        ]
  buildExpressionParser table term
  where
    term = do
      base <- parens (withState (set inArgs False . set inFieldInit False . set inTuple False) expr)
         <|> try unqualifiedFunCall <|> baseExpr <|> ifExpr
         <|> try newExpr <|> newConstrExpr <|> methodExpr <|> invariantExpr <|> typedecl
         <?> "basic expression"
      try (combExpr base) <|> return base
    binary  name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
    prefix  name fun       = Prefix (do{ reservedOp name; return fun })
    postfix name fun       = Postfix (do{ reservedOp name; return fun })

combExpr :: Expr -> Parser Expr
combExpr prefix = do
  next <- try (ECall prefix <$> (symbol "." *> identifier)
                            <*> callParams)
      <|> try (EIdx prefix <$> (symbol "[" *> expr <* symbol "]"))
      <|> try (EProj prefix <$> (symbol "." *> identifier))
      <|> pure ENop
  if next == ENop then return prefix else combExpr next

tuple :: Parser Expr
tuple = do
  symbol "<"
  elts <- withState (set inTuple True) $ expr `sepBy` symbol ","
  symbol ">"
  return $ ETuple elts


baseExpr :: Parser Expr
baseExpr = EVar <$> identifier <|> EConst <$> value
       <|> tuple
       <?> "number, variable, or tuple"

projExpr :: Parser Expr
projExpr = EProj <$> baseExpr <*> (symbol "." *> identifier)

projExpr' :: Expr -> Parser Expr
projExpr' expr = EProj expr <$> (symbol "." *> identifier)

ifExpr :: Parser Expr
ifExpr = EIf <$> (reserved "if" *> symbol "(" *> expr <* symbol ")")
             <*> ifArm
             <*> (reserved "else" *> ifArm)
         <?> "conditional"
  where ifArm = do
          inBraces <- (symbol "{" *> pure True) <|> pure False
          e <- expr
          if inBraces then symbol "}" else pure ""
          return e

unqualifiedFunCall :: Parser Expr
unqualifiedFunCall = ECall (EConst VNil) <$> identifier <*> callParams

callParams :: Parser [Expr]
callParams = (symbol "(" *> withState (set inArgs True) (expr `sepBy` symbol ",") <* symbol ")")

typ :: Parser Type
typ = (reserved "int" *> pure TInt)
  <|> (symbol "*" *> pure TAny)
  <|> (TTuple <$> (symbol "<" *> typ `sepBy` symbol "," <* symbol ">"))
  <|> (TMap <$> (reserved "map" *> typ) <*> typ)
  <|> (TNamed <$> identifier)
  <?> "type"

field :: Parser Field
field = do
  isConst <- try (reserved "const" *> pure True) <|> pure False
  id <- identifier
  typ <- try (symbol ":" *> typ) <|> pure TAny
  init <- try (symbol "=" *> expr) <|> pure (EVar id)
  return $ Field { _fieldName = id
                 , _fieldInit = init
                 , _fieldType = typ
                 , _immutable = isConst }

-- | Fails if list elements are not unique under given function; returns its argument unchanged otherwise
uniqueBy :: (Show a, Eq b) => (a -> b) -> [a] -> Parser [a]
uniqueBy f lst | length (nubBy ((==) `on` f) lst) == length lst = return lst
               | otherwise = fail $ "List elements not unique: " ++ show lst


uniqueFields :: [Field] -> Parser [Field]
uniqueFields = uniqueBy (^. fieldName)

newExpr :: Parser Expr
newExpr = ENew <$> (reserved "new" *> symbol "(" *>
                    withState (set inFieldInit True) (uniqueFields =<< field `sepBy` symbol ",") <* symbol ")")
               <*> (symbol "{" *> (foldr ESeq ENop <$> many expr) <* symbol "}")

constrArg :: Parser (Var, Expr)
constrArg = (,) <$> (identifier <?> "constructor parameter name") <*> (symbol "=" *> expr)
        <?> "constructor argument (x = e)"

newConstrExpr :: Parser Expr
newConstrExpr = ENewConstr <$> (reserved "new" *> identifier)
                           <*> (symbol "(" *>
                                withState (set inFieldInit True)
                                          ((uniqueBy fst =<< constrArg `sepBy` symbol ",")
                                           <?> "constructor keyword arguments") <*
                                symbol ")")

methodArg :: Parser (String, Type)
methodArg = (do
  id <- identifier
  typ <- try (symbol ":" *> typ) <|> pure TAny
  return (id, typ)) <?> "method argument"

methodExpr :: Parser Expr
methodExpr = EMethod <$> (reserved "method" *> identifier)
                     <*> (symbol "(" *> methodArg `sepBy` symbol "," <* symbol ")")
                     <*> (symbol "{" *> expr <* symbol "}")
                     <*> pure False

invariantExpr :: Parser Expr
invariantExpr = EMethod <$> (reserved "invariant" *> identifier)
                        <*> (symbol "(" *> methodArg `sepBy` symbol "," <* symbol ")")
                        <*> (symbol "{" *> expr <* symbol "}")
                        <*> pure True

-- | Split field declarations into formal parameters for type declarations
-- and constant field initializations. Fails if there is a non-constant
-- initialization. This function is only monadic in order to report
-- such invalid fields as a parse error.
splitTypeDeclFields :: [Field] -> Parser ([(Var, Type)], [(Var, Value)])
splitTypeDeclFields [] = return ([], [])
splitTypeDeclFields (fld : flds) = do
  (args, values) <- splitTypeDeclFields flds
  if fld ^. fieldInit == EVar (fld ^. fieldName)
        -- the field parser defaults to the field's name if no initialization expression is given
  then return ((fld ^. fieldName, fld ^. fieldType) : args, values)
  else case fld ^. fieldInit of
         EConst v -> return (args, (fld ^. fieldName, v) : values)
         e -> fail $ "Non-constant field initialization in type declaration: " ++ show e

typedecl :: Parser Expr
typedecl = do
  reserved "type"
  typeName <- identifier
  symbol "=" *> reserved "new"
  fields <- symbol "(" *> withState (set inFieldInit True) (field `sepBy` symbol ",") <* symbol ")"
  body <- symbol "{" *> expr <* symbol "}"
  (formals, values) <- splitTypeDeclFields fields
  let result = ETypeDecl { _typedeclName = typeName
                         , _typedeclFormals = formals
                         , _typedeclValues = values
                         , _typedeclBody = body }
  -- Maybe move this check out of the parser to somewhere else:
  if (S.null . fst . varBindings $ result)
    then return result
    else fail "Free variables in type declaration"

program :: Parser Expr
program = foldr1 ESeq <$> many1 expr

overrideMethod :: Parser Diff
overrideMethod = OverrideMethod <$> methodExpr

diffs :: Parser [Diff]
diffs = many1 overrideMethod

modField :: Parser [Diff]
modField = do
  reserved "new" *> symbol "(" *> symbol "..."  *> symbol ","
  fieldOp <- try (NewField <$> field) <|> (reserved "delete" *>
                                           (DeleteField <$> identifier))
  symbol ")"
  symbol "{" *> symbol "..."
  rest <- many overrideMethod
  symbol "}"
  return $ fieldOp : rest

initialParserState :: ParserState
initialParserState = ParserState { _inTuple = False, _inFieldInit = False, _inArgs = False }

diffOrExpr :: Parser ProofPart
diffOrExpr =
  try (PDiff <$> modField)
  <|>
  lookAhead (reserved "new") *> (Prog <$> expr)
  <|>
  PDiff <$> many1 overrideMethod
  <|> Prog <$> expr

parse :: Parser a -> String -> a
parse p s =
  case runParser (whiteSpace *> p <* whiteSpace <* eof) initialParserState "" s of
    Left err -> error $ "Parse error: " ++ show err
    Right expr -> expr

parseExpr :: String -> Expr
parseExpr s = parse program s

parseFile :: MonadIO m => FilePath -> m Expr
parseFile file = parseExpr <$> liftIO (readFile file)

parseProofPart :: String -> ProofPart
parseProofPart = parse diffOrExpr
