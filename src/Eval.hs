{-# Options_GHC -Wall #-}
{-# Language TupleSections #-}
module Eval where

import qualified Data.Map as M
import           Expr
import           Control.Applicative ((<|>))
import           Data.List (foldl')
import           Env
import           Errors

import qualified Control.Monad.Except as E

-------------------------------------------------------

eval :: Monad m => Env -> Expr -> E.ExceptT [ProgramError] m Result
eval env expr = case expr of
  EVar x -> pure $ apply env x

  EVal x -> pure $ RVal x

  EAdd e1 e2 -> do
    r1 <- eval env e1
    r2 <- eval env e2
    case (r1,r2) of
      (RVal (I x), RVal (I y)) -> pure $ RVal (I (x + y))
      (_, _)               -> E.throwError $ [evalError $ "add failed"]


  EMul e1 e2 -> do
    r1 <- eval env e1
    r2 <- eval env e2
    case (r1,r2) of
      (RVal (I x), RVal (I y)) -> pure $ RVal (I (x * y))
      (_, _)               -> E.throwError $ [evalError $ "mul failed"]

  ELEq e1 e2 -> do
    r1 <- eval env e1
    r2 <- eval env e2
    case (r1,r2) of
      (RVal (I x), RVal (I y)) -> pure $ RVal (B (x <= y))
      (_, _)               -> E.throwError $ [evalError $ "leq failed"]

  ECond e1 e2 e3 -> do
    r1 <- eval env e1
    case r1 of
      RVal (B True)  -> eval env e2
      RVal (B False) -> eval env e3
      _              -> E.throwError $ [evalError $ "cond failed"]

  EAbs x e -> pure $ RAbs env x e

  EApp e1 e2 -> do
    r1 <- eval env e1
    case r1 of
      RAbs env' x b -> do
        r2 <- eval env e2
        let env'' = env' `union` env
        eval (insert x r2 env'') b

      _    -> E.throwError $ [evalError $ "app failed"]

  ELet x e1 e2 -> do
    r1  <- eval env e1
    let env' = insert x r1 env
    eval env' e2

  EMatch e1 cs -> do
    r <- eval env e1
    let bindings = fmap (\(p,b) -> (,b) <$> patternMatch r p) cs 
    let firstMatch = foldl' (<|>) Nothing bindings
    case firstMatch of
      Just (env',b) -> eval (env' `union` env) b
      Nothing -> E.throwError $ [evalError "asdasdsad"]


  ERecEmpty -> pure $ RRec M.empty
  EAltEmpty -> pure $ RRec M.empty

  ERecExt l e1 e2 -> do
    r1 <- eval env e1
    r2 <- eval env e2
    case r2 of
      RRec m
        | l `elem` M.keys m -> pure $ RRec (M.adjust (r1:) l m)
        | otherwise         -> pure $ RRec (M.insert l [r1] m)

      _    -> E.throwError $ [evalError $ "rec failed"]

  ERecSel e1 l -> do
    r1 <- eval env e1
    case r1 of
      RRec m
        | l `elem` M.keys m -> pure $ head (m M.! l)

      _ -> E.throwError $ [evalError "rec sel failed"]
  
  ERecRem e1 l -> do
    r1 <- eval env e1
    case r1 of
      RRec m -> case M.lookup l m of
        Just [_] -> pure $ RRec (M.delete l m)
        Just _   -> pure $ RRec (M.adjust tail l m)
        _        -> E.throwError $ [evalError "kds;aksd"]

      _       -> E.throwError $ [evalError "kds;aksd"]

  EInj l e -> do
    r <- eval env e
    pure $ RAlt (Just (l,r))

  EEmb _ e -> eval env e 

---------------------------------------------------
patternMatch :: Result -> Pattern -> Maybe Env
patternMatch (RVal r) (PVal p)
            | p == r      = pure empty
            | otherwise   = Nothing
patternMatch r (PVar x)   = pure $ Env (M.singleton x r)
patternMatch _ PEmpty     = pure empty
patternMatch r (PAs x p)  = insert x r <$> patternMatch r p
patternMatch e (PAlt l p) = case e of
    RAlt (Just (l',r))
            | l == l'    -> patternMatch r p
    _                    -> Nothing
patternMatch _ _ = Nothing
