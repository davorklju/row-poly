module Expr where

import qualified Data.Map as M

type Name = String
type Pos = (Int,Int)


data Value
    = I Int
    | B Bool
    | Unit
  deriving (Eq, Show)


data Pattern
    = PVal Value
    | PVar Name
    | PEmpty
    | PAs Name Pattern
    | PAlt Name Pattern
    | PRec [(Name,Pattern)]
  deriving Show


data Statement
    = TypeDef Name [TType] Type
    | LetDef Name Expr
  deriving Show


data Expr
    = EVal Value
    | EVar Name

    | EAdd Expr Expr
    | EMul Expr Expr
    | ELEq Expr Expr 
    | ECond Expr Expr Expr

    | EAbs Name Expr
    | EApp Expr Expr

    | ELet Name Expr Expr

    | EMatch Expr [(Pattern,Expr)]

    | ERecEmpty 
    | EAltEmpty

    | ERecSel Expr Name -- {..}.l
    | ERecRem Expr Name -- {..} // x
    | ERecExt Name Expr Expr -- {l=x|r}

    | EInj Name Expr -- <l=x>
    | EEmb Name Expr -- <l|r>


type TType = (Name,Kind)

data Type
    = TVar TType
    | TVal TType
    | TArr Type Type
    | TRec Type
    | TAlt Type
    | TRowNull
    | TRowExt Name Type Type
    | TApp Type Type
  deriving (Eq,Ord)


data Kind
    = KStar
    | KRow
    | KArr Kind Kind
    | KVar Name
  deriving (Eq,Ord)


------------------------------------------------------

instance Show Kind where
  show KStar = "*"
  show KRow = "row"
  show (KArr l r)
    | KArr _ _ <- l = "(" ++ show l ++ ") -> " ++ show r
    | otherwise     = show l ++ " -> " ++ show r
  show (KVar s) = s

instance Show Type where
  show (TVar (n,k)) = n ++ ":" ++ show k
  show (TVal (n,k)) = n ++ ":" ++ show k
  show (TArr a b) = case a of
    TArr _ _ -> "(" ++ show a ++ " ) -> " ++ show b
    _        -> show a ++ " -> " ++ show b
  show (TRec r) = "{" ++ show r ++ "}"
  show (TAlt r) = "<" ++ show r ++ ">"
  show TRowNull = "(/)"
  show (TRowExt n t r) = n ++ ":" ++ show t ++ " | " ++ show r
  show (TApp a b) = show a ++ " " ++ show b


instance Show Expr where
    show (EVal v) = show v
    show (EVar v) = v

    show (EAdd e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
    show (EMul e1 e2) = show e1 ++ " * " ++ show e2 
    show (ELEq e1 e2) = show e1 ++ " <= " ++ show e2 
    show (ECond e1 e2 e3) = "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3

    show (EAbs n e) = "lam " ++ n ++ " . " ++ show e
    show (EApp e1 e2) = show e1 ++ " " ++ show e2

    show (ELet n e1 e2) = "let " ++ show n ++ " = " ++ show e1 ++ " in " ++ show e2

    show (EMatch e0 cs) =
      "match " ++ show e0 ++ concat (map ("|" ++ ) $ map show cs) ++ "end"

    show ERecEmpty = "{}"
    show EAltEmpty = "<>"

    show (ERecSel e n) = show e ++ "." ++ n
    show (ERecRem e n) = show e ++ "//" ++ n
    show (ERecExt n e1 e2) = "{" ++ n ++ "=" ++ show e1 ++ "|" ++ show e2 ++ "}"

    show (EInj n e) = "<" ++ n ++ "=" ++ show e ++ ">"
    show (EEmb n e) = "<" ++ n ++ "|" ++ show e ++ ">"






