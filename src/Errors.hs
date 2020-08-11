module Errors where

import Expr (Pos)

data ParseError = PError !Pos !String
  deriving (Eq,Show)

newtype KindError = KE String
  deriving (Eq,Show)

newtype TypeError = TE String
  deriving (Eq,Show)

newtype EvalError = EE String
  deriving (Eq,Show)

data ProgramError 
    = ParseError ParseError
    | KindError KindError
    | TypeError TypeError
    | EvalError EvalError
  deriving (Eq,Show)

kindError :: String -> ProgramError
kindError s = KindError (KE s)

parseError :: Pos -> String -> ProgramError
parseError p s = ParseError (PError p s)

typeError :: String -> ProgramError
typeError s = TypeError (TE s)

evalError :: String -> ProgramError
evalError s = EvalError (EE s)
