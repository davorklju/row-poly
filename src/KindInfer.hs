{-# Options_GHC -Wall #-}
{-# Language DeriveFunctor,GeneralizedNewtypeDeriving  #-}
module KindInfer where

import Expr
import Errors
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Control.Monad.Except as E
import qualified Control.Monad.State  as St
import qualified Infer as I

newtype Sub = Sub { unSub :: M.Map Name Kind } deriving Show
newtype KindEnv = KindEnv { unKindEnv :: M.Map Name Kind } deriving Show

---------------------------------------------------------

emptySub :: Sub
emptySub = Sub M.empty

compose :: Sub -> Sub -> Sub
compose s@(Sub m2) (Sub m1) =
    Sub $ fmap (apply s) m1 `M.union` m2


---------------------------------------------------------

emptyEnv :: KindEnv
emptyEnv = KindEnv M.empty

class Apply a where
  apply :: Sub -> a -> a
  free :: a -> S.Set Name


instance Apply Kind where
  apply _ KStar = KStar
  apply _ KRow = KRow
  apply (Sub m) (KVar x) = maybe (KVar x) id $ M.lookup x m
  apply s (KArr a b) = KArr (apply s a) (apply s b) 

  free (KVar x)   = S.singleton x
  free (KArr a b) = free a `S.union` free b
  free  _         = S.empty


instance Apply KindEnv where
  apply s (KindEnv m) = KindEnv (fmap (apply s) m)
  free (KindEnv m) = S.unions (free <$> M.elems m)

----------------------------------------------------------

newtype Eval a = Eval { unEval :: St.StateT (Int,Sub) (E.ExceptT [ProgramError] IO) a }
  deriving (Functor,Applicative,Monad
           , E.MonadError [ProgramError]
           , E.MonadIO
           , St.MonadState (Int,Sub)
           )

runEval :: Eval a -> IO (Either [ProgramError] (a,(Int,Sub)))
runEval = E.runExceptT . flip St.runStateT (0,emptySub) . unEval


fresh :: Name -> Eval Kind
fresh prefix = do
  (i,s) <- St.get
  St.put (i+1,s)
  pure $ KVar (prefix ++ show i)

bindVar :: Name -> Kind -> Eval Sub
bindVar x k = pure $ Sub (M.singleton x k)

mgu :: Kind -> Kind -> Eval Sub
mgu (KVar x) k = bindVar x k
mgu k (KVar x) = bindVar x k
mgu (KArr a b) (KArr a' b') = do
  s1 <- mgu a a'
  s2 <- mgu (apply s1 b) (apply s1 b')
  pure (s2 `compose` s1)
mgu a b
  | a == b    = pure emptySub
  | otherwise = E.throwError [kindError "kind unification failed"]


appendSub :: Sub -> Eval ()
appendSub s = St.modify (\(i,s') -> (i,compose s s'))

unify :: Kind -> Kind -> Eval ()
unify k1 k2 = do
  (_,s) <- St.get
  s' <- mgu (apply s k1) (apply s k2)
  appendSub s'

--------------------------------------------------------

infer :: KindEnv -> Type -> Eval (Kind,Sub)
infer env0 t = do
  let ftv = S.toList $ (S.map fst (I.free t)) S.\\ free env0
  let ts = map KVar ftv
  let env1 = KindEnv $ (unKindEnv env0) `M.union` M.fromList (zip ftv ts)
  k <- ki env1 t
  s <- snd <$> St.get
  pure (k,s)

ki :: KindEnv -> Type -> Eval Kind
ki env0 t0 = do
    (_,s) <- St.get
    k <- kiBase (apply s env0) t0
    (_,s') <- St.get
    pure (apply s' k)
  where
    kiBase (KindEnv m) (TVar (x,_)) = case M.lookup x m of
        Just k  -> pure k
        Nothing -> E.throwError [kindError $ "unbound kind variable: " ++ x] --should never happen

    kiBase _ (TVal (_,k)) = pure k

    kiBase env (TArr a b) = do
      k1 <- ki env a
      k2 <- ki env b
      unify k1 k2
      unify k1 KStar
      pure KStar

    kiBase env (TRec x) = do
      k1 <- ki env x
      unify k1 KRow
      pure KStar

    kiBase env (TAlt x) = do
      k1 <- ki env x
      unify k1 KRow
      pure KStar

    kiBase _ TRowNull = pure KRow

    kiBase env (TRowExt _ t r) = do
      k1 <- ki env t
      k2 <- ki env r
      unify k1 KStar
      unify k2 KRow
      pure KRow

    kiBase env (TApp f x) = do
      k1 <- ki env f
      k2 <- ki env x
      ta <- fresh "a"
      unify k1 (KArr k2 ta)
      pure ta









