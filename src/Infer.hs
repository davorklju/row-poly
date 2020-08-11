{-# Options_GHC -Wall #-}
{-# Language DeriveFunctor,GeneralizedNewtypeDeriving #-}
{-# Language TupleSections #-}
module Infer where

import Expr
import Errors
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L

import Control.Monad.State
import Control.Monad.Except
import Data.Function (on)


kindOf :: Type -> Kind
kindOf (TVar (_,k)) = k
kindOf (TVal (_,k)) = k
kindOf (TArr _ _)   = KStar
kindOf (TRec _)     = KStar
kindOf (TAlt _)     = KStar
kindOf TRowNull     = KRow
kindOf (TRowExt _ _ _) = KRow
kindOf (TApp f _)
    | KArr _ k <- kindOf f = k
    | otherwise            = error "asdasd"

-------------------------------------------------

data Poly = Poly [TType] Type deriving Show

newtype Sub = Sub { unSub :: M.Map TType Type } deriving Show

newtype TypeEnv = TypeEnv { unTypeEnv :: M.Map Name Poly } deriving Show

-----------------------------------------------------
empty :: Sub
empty = Sub M.empty

compose :: Sub -> Sub -> Sub
compose s@(Sub m2) (Sub m1) =
  Sub $ fmap (apply s) m1 `M.union` m2

dom :: Sub -> S.Set Name
dom = S.fromList . map fst . M.keys . unSub
--------------------------------------------
emptyEnv :: TypeEnv
emptyEnv = TypeEnv M.empty

generalize :: TypeEnv -> Type -> Poly
generalize env t = Poly ftv t
  where ftv = S.toList $ free t S.\\ free env

append :: Name -> Type -> TypeEnv -> TypeEnv
append n t env = appendPoly n (Poly [] t) env

appendPoly :: Name -> Poly -> TypeEnv -> TypeEnv
appendPoly n p env = TypeEnv $ M.insert n p (unTypeEnv env)
----------------------------------------------------------------------------------

class Apply a where
  apply :: Sub -> a -> a

instance Apply Type where
  apply s (TVar x)        = maybe (TVar x) id $ M.lookup x (unSub s)
  apply _ (TVal c)        = TVal c
  apply s (TArr t1 t2)    = TArr (apply s t1) (apply s t2)
  apply s (TRec r)        = TRec (apply s r)
  apply s (TAlt r)        = TAlt (apply s r)
  apply _ TRowNull        = TRowNull
  apply s (TRowExt l t r) = TRowExt l (apply s t) (apply s r)
  apply s (TApp t1 t2)    = TApp (apply s t1) (apply s t2)

instance Apply TypeEnv where
  apply s (TypeEnv m) = TypeEnv (fmap (apply s) m)

instance Apply Poly where
  apply s (Poly vs t) = Poly vs (apply s' t)
    where s' = Sub $ foldr M.delete (unSub s) vs

-------------------------------------

class Free a where
  free :: a -> S.Set TType

instance Free Type where
  free (TVar x)          = S.singleton x
  free (TRec t)          = free t
  free (TAlt t)          = free t
  free (TArr t1 t2)      = free t1 `S.union` free t2
  free (TRowExt _ t1 t2) = free t1 `S.union` free t2
  free TRowNull          = S.empty
  free (TVal _)          = S.empty
  free (TApp t1 t2)      = free t1 `S.union` free t2


instance Free TypeEnv where
  free (TypeEnv m) = S.unions (free <$> M.elems m)


instance Free Poly where
  free (Poly vs t) = free t S.\\ S.fromList vs

---------------------------------------------------------------

newtype Eval a = Eval { unEval :: StateT (Int,Sub) (ExceptT [ProgramError] IO) a }
  deriving ( Functor, Applicative, Monad
           , MonadState (Int,Sub)
           , MonadError [ProgramError]
           , MonadIO
           )

runEval :: Eval a -> IO (Either [ProgramError] (a, (Int,Sub)))
runEval = runExceptT . flip runStateT (0,empty) . unEval


fresh :: Name -> Kind -> Eval Type
fresh prefix k = do
  let p = takeWhile (`elem` ['a'..'z']) prefix
  (i,s) <- get
  put (i + 1,s)
  pure $ TVar (p ++ show i, k)

-------------------------------------------------------------

appendSub :: Sub -> Eval ()
appendSub s1 = do
  (i,s0) <- get
  put (i,s1 `compose` s0)


unify :: Type -> Type -> Eval ()
unify t1 t2 = do
    s0 <- snd <$> get
    s1 <- mgu (apply s0 t1) (apply s0 t2)
    appendSub s1
  where
    mgu (TVar x) e = bindVar x e
    mgu e (TVar x) = bindVar x e

    mgu (TArr a b) (TArr a' b') = do
      s1 <- mgu a a'
      s2 <- mgu (apply s1 b) (apply s1 b')
      pure (s2 `compose` s1)

    mgu (TApp a b) (TApp a' b') = do
      s1 <- mgu a a'
      s2 <- mgu (apply s1 b) (apply s1 b')
      pure (s2 `compose` s1)

    mgu (TRec a) (TRec b) = mgu a b
    mgu (TAlt a) (TAlt b) = mgu a b

    mgu r@TRowExt{} s = unifyRow r s
    mgu s r@TRowExt{} = unifyRow r s

    mgu a b
        | a == b    = pure empty
        | otherwise = throwError [typeError $ "unification failed on: " ++ show a ++ " and " ++ show b]

----
bindVar :: TType -> Type -> Eval Sub
bindVar x e
  | e == (TVar x)   = pure empty
  | x `elem` free e = 
      throwError [typeError $ "occurs check failed: " ++ show x ++ " in " ++ show e]
  | kindOf (TVar x) /= kindOf e =
      throwError [typeError $ "kinds do not match for: " ++ show x ++ " and " ++ show e ]
  | otherwise       = pure $ Sub (M.singleton x e)
-----
notDistinctPrefix :: Type -> Eval () -- prevent {x:t|r} ~ {y:s|r} => {y:s|b} ~ {x:t|b}
notDistinctPrefix t = do             
  s <- snd <$> get
  case t of
    TVar (x,_) | x `elem` dom s ->
        throwError [typeError "records with common tail, but distinc head"]
    _ -> pure ()

unifyRow :: Type -> Type -> Eval Sub
unifyRow (TRowExt l e r) s = do
    (e',r') <- findLabel l s
    notDistinctPrefix r
    unify e e'
    unify r r'
    snd <$> get
unifyRow _ _ = throwError [typeError $ "this cannot happen"]
-----
findLabel :: Name -> Type -> Eval (Type,Type)
findLabel lbl ty = do
    s <- snd <$> get
    case apply s ty of
      TRowExt l' t r
        | lbl == l' -> pure (t,r)
        | otherwise -> do
            (a,b) <- findLabel lbl r
            pure (a, TRowExt l' t b)

      TVar x -> do
        ta <- fresh "a" KStar
        tr <- fresh "r" KRow
        appendSub $ Sub (M.singleton x (TRowExt lbl ta tr))
        pure (ta,tr)

      _ -> throwError [typeError $ "could not find label: " ++ lbl]
-------------------------------------------------------------------------
patternMatch :: TypeEnv -> Type -> Pattern -> Eval TypeEnv
patternMatch env0' t0' p0' = do
      s0 <- snd <$> get
      patternmatchBase (apply s0 env0') (apply s0 t0') p0'
  where
    patternmatchBase env t (PVar x) =
      pure (append x t env)

    patternmatchBase env t (PAs n p) =
      let env' = append n t env in patternmatchBase env' t p

    patternmatchBase env t (PVal v) = do
      t' <- tiVal v
      unify t t'
      pure env

    patternmatchBase env t (PAlt l p) = do
      ta <- fresh "a" KStar
      tr <- fresh "r" KRow
      unify t (TAlt $ TRowExt l ta tr)
      env' <- patternMatch env ta p
      pure $ append l ta env'

    patternmatchBase env t (PRec ps) = rfold $ \(l,p) resM -> do
        env0 <- resM
        ta <- fresh "a" KStar
        tr <- fresh "r" KRow
        unify t (TRec $ TRowExt l ta tr)
        env1 <- patternMatch env0 ta p
        pure $ append l ta env1
      where
        rfold f = foldr f (pure env) ps

    patternmatchBase env _ PEmpty = pure env
----------------------------------------------------------------------------------

tiOp :: TypeEnv -> Expr -> Expr -> Name -> Name -> Eval Type
tiOp env a b targ tout = do
  t1 <- ti env a
  t2 <- ti env b
  unify t1 t2
  unify t2 (TVar (targ,KStar))
  pure $ TVal (tout,KStar)

--------
tiVal :: Value -> Eval Type
tiVal v = pure $ case v of
    I _  -> TVal ("int",KStar)
    B _  -> TVal ("bool",KStar)
    Unit -> TVal ("unit",KStar)
--------

ti :: TypeEnv -> Expr -> Eval Type
ti env0' e0' = do
    s0 <- snd <$> get
    t <- tiBase (apply s0 env0') e0'
    s1 <- snd <$> get
    pure (apply s1 t)
  where
    tiBase _ (EVal v) = tiVal v

    tiBase env (EAdd a b) = tiOp env a b "int" "int"
    tiBase env (EMul a b) = tiOp env a b "int" "int"
    tiBase env (ELEq a b) = tiOp env a b "int" "bool"
    tiBase _    ERecEmpty = pure (TRec TRowNull)
    tiBase _    EAltEmpty = pure (TAlt TRowNull)

    tiBase env (EVar x) = case M.lookup x (unTypeEnv env) of
        Nothing -> throwError [typeError $ "unbound variable: " ++ x]
        Just (Poly vs t) -> do
          ts <- traverse (uncurry fresh) vs
          let s = Sub (M.fromList (zip vs ts))
          pure (apply s t)

    tiBase env (ECond a b c) = do
        t1 <- ti env a
        t2 <- ti env b
        t3 <- ti env c
        unify t1 (TVal ("bool",KStar))
        unify t2 t3
        pure t3

    tiBase env (EAbs x e) = do
      tv <- fresh x KStar
      let env' = append x tv env
      t1 <- ti env' e
      pure (TArr tv t1)

    tiBase env (EApp e1 e2) = do
      tv <- fresh "a" KStar
      t1 <- ti env e1
      t2 <- ti env e2
      unify t1 (TArr t2 tv)
      pure tv

    tiBase env (ELet x e1 e2) = do
      t1 <- ti env e1
      let sc   = generalize env t1
      let env' = appendPoly x sc env
      t2 <- ti env' e2
      pure t2

    tiBase env0 (EMatch e1 pats) = do -- match e1 | p -> e2
      ta <- fresh "a" KStar -- type of the result
      t0 <- ti env0 e1 -- type of the input
      _ <- flip traverse pats $ \(p,e) -> do
        env' <- patternMatch env0 t0 p
        t <- ti env' e
        unify t ta
      pure ta

    tiBase env (ERecSel r l) = do
      tv <- fresh "t" KStar
      rv <- fresh "r" KRow
      t1 <- ti env r
      unify t1 (TRec (TRowExt l tv rv))
      pure tv

    tiBase env (ERecRem e l) = do
      tv <- fresh "t" KStar
      rv <- fresh "r" KRow
      t1 <- ti env e
      unify t1 (TRec (TRowExt l tv rv))
      pure (TRec rv)

    tiBase env (ERecExt l e r) = do
      tv <- fresh "r" KRow
      t1 <- ti env e
      t2 <- ti (env) r
      unify t2 (TRec tv)
      pure (TRec $ TRowExt l t1 tv)

    tiBase env (EInj l e) = do
      tv <- fresh "r" KRow
      t1 <- ti env e
      pure (TAlt $ TRowExt l t1 tv)

    tiBase env (EEmb l e) = do
      tv <- fresh "t" KStar
      rv <- fresh "r" KRow
      t1 <- ti env e
      unify t1 (TAlt $ rv)
      pure (TAlt $ TRowExt l tv rv)

---------------------------------------------

inference :: Expr -> Eval Type
inference e = inferWithEnv (TypeEnv M.empty) e

inferWithEnv :: TypeEnv -> Expr -> Eval Type
inferWithEnv env e = do
  t <- ti env e
  s <- snd <$> get
  simpleFTV (apply s t)


simpleFTV :: Type -> Eval Type
simpleFTV ty = do
      let ftvs = S.toList $ free ty
      let sub = toSub (groupByPrefix ftvs)
      pure (apply sub ty)
  where
    toSub = Sub . M.unions . map (reName . zip [0..])
    stripPrefix = takeWhile (`elem` ['a'..'z'])
    groupByPrefix = L.groupBy ((==) `on` (stripPrefix . fst)) 

    reName :: [(Int,TType)] -> M.Map TType Type
    reName xs          = M.unions (map sub xs)
      where
        sub (0,(n,k)) = M.singleton (n,k) (TVar (stripPrefix n          , k))
        sub (i,(n,k)) = M.singleton (n,k) (TVar (stripPrefix n ++ show i, k))










