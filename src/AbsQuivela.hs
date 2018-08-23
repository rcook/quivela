

module AbsQuivela where

-- Haskell module generated by the BNF converter




newtype Id = Id String deriving (Eq, Ord, Show, Read)
data Val = VInt Integer | VMap
  deriving (Eq, Ord, Show, Read)

data Expr
    = EVar Id
    | EConst Val
    | ETuple [Expr]
    | ETupleProj Expr Expr
    | EProj Expr Expr
    | EIdx Expr Expr
    | ECall Expr [Expr]
    | ENot Expr
    | EEq Expr Expr
    | EAssign Expr Expr
    | EMul Expr Expr
    | EDiv Expr Expr
    | EAdd Expr Expr
    | ESub Expr Expr
    | EPostIncr Expr
    | EOr Expr Expr
    | EAmp Expr Expr
    | EMethod Id [Arg] Expr
    | ESeq Expr Expr
    | ENew [Init] Expr
  deriving (Eq, Ord, Show, Read)

data Arg = UArg Id | TArg Id Type
  deriving (Eq, Ord, Show, Read)

data Init = UInit InitMod Id Expr | TInit InitMod Id Type Expr
  deriving (Eq, Ord, Show, Read)

data InitMod = ConstMod | NoMod
  deriving (Eq, Ord, Show, Read)

data Type
    = TInt | TTuple [Type] | TAny | TMap Type Type | TNamed Id
  deriving (Eq, Ord, Show, Read)

