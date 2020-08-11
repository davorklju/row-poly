module Env where

import Expr
import qualified Data.Map as M


newtype Env = Env (M.Map Name Result)
  deriving Show

data Result
    = RVal Value
    | RAbs Env Name Expr
    | RAlt (Maybe (Name, Result))
    | RRec (M.Map Name [Result])
  deriving Show



find :: Name -> Env -> Maybe Result
find x (Env m) = M.lookup x m

insert :: Name -> Result -> Env -> Env
insert n r (Env m) = Env (M.insert n r m)

union :: Env -> Env -> Env
union (Env m1) (Env m2) = Env (m1 `M.union` m2)

(//) :: Env -> Name -> Env
(Env m) // x = Env (M.delete x m)

empty :: Env
empty = Env M.empty

apply :: Env -> Name -> Result
apply (Env m) x = case M.lookup x m of
    Just r -> r
    _      -> error $ "unbound variable: " ++ x

