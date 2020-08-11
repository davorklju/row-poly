{-# Options_GHC -Wall #-}
{-# Language DeriveFunctor #-}
{-# Language TypeFamilies,FlexibleContexts#-}
{-# Language MultiParamTypeClasses, FunctionalDependencies #-}
{-# Language FlexibleInstances ,UndecidableInstances #-}
module Sub where
import qualified Data.Map as M
import qualified Data.Set as S


data EqT a = EqT { eq' :: a -> a -> Bool }
data OrdT a = OrdT { super'EqT :: EqT a, lt' :: a -> a -> Bool }


int'Eq :: EqT Int
int'Eq = EqT (==)

int'Ord :: OrdT Int
int'Ord = OrdT int'Eq (<)


qqq :: Int -> String
qqq = undefined

ppp :: String -> Bool
ppp = undefined

foo :: (a,b,c) -> (b,c,a)
foo (x,y,z) = (y,z,x)


----------------------

data App k t a = App {
     apply' :: M.Map k t -> a -> a,
     free'  :: a -> S.Set k
  }

freeA :: App k t a -> a -> S.Set k
freeA m = free' m

applyA :: App k t a -> M.Map k t -> a -> a
applyA m = apply' m


appType :: App KTag Type Type
appType = App app' fr' where
  app' m (TVar k)   = maybe (TVar k) id $ M.lookup k m
  app' _ (TVal k)   = TVal k
  app' s (TApp a b)  = TApp (app' s a) (app' s b)

  fr' (TVar k)    = S.singleton k
  fr' (TVal _)    = S.empty
  fr' (TApp a b)  = fr' a `S.union` fr' b

appKind :: App Name Kind Kind
appKind = App app' fr' where
  app' m (KVar k)   = maybe (KVar k) id $ M.lookup k m
  app' _ (KVal k)   = KVal k
  app' s (KArr a b) = KArr (app' s a) (app' s b)

  fr' (KVar k)    = S.singleton k
  fr' (KVal _)    = S.empty
  fr' (KArr a b)  = fr' a `S.union` fr' b


appPoly :: App KTag Type Poly
appPoly = App app' fr' where
  app' m (Poly vs t) = Poly vs $ apply' appType (foldr M.delete m vs) t

  fr' (Poly vs t) = free' appType t S.\\ S.fromList vs


appEnv :: Ord k => App k t a -> App k t (Env a)
appEnv super = App app' fr' where
  app' m (Env e) = Env (fmap (apply' super m) e)

  fr' (Env e) = S.unions $ fmap (free' super) (M.elems e)



spec :: Monad m => Poly -> m Type
spec (Poly vs t) = do
    kts <- flip traverse vs $ \x -> do
      v <- fresh undefined
      pure (x,v)
    let s = M.fromList $ kts
    pure (app s t)
  where
    app = apply' appType


gen :: Monad m => Env Poly -> Type -> m Poly
gen env t = do
    let ftv = S.toList (freeA appType t S.\\ freeA (appEnv appPoly) env)
    pure $ Poly ftv t

-------------

type Name = String
type KTag = (Name,Kind)


data Expr = Expr

data Type
    = TVal KTag
    | TVar KTag
    | TApp Type Type
  deriving (Eq,Show)

data Kind
    = KVal Name
    | KVar  Name
    | KArr Kind Kind
  deriving (Eq,Ord,Show)

---------------------------------
data Poly = Poly [KTag] Type

newtype Env t = Env { unEnv :: M.Map Name t }
  deriving (Show,Functor)

newtype Sub a = Sub { unSub :: M.Map (Key a) a }

-----
type family Key t where
  Key Expr = Name
  Key Kind = Name

  Key Type = Name
  Key Poly = Name

  Key (Env t) = Key t
  
--------------------------------

class (Ord (Key t)) => Apply t a | a -> t where
  apply :: Sub t -> a -> a
  free :: a -> S.Set (Key t)

--------------

(@@) :: Apply a a => Sub a -> Sub a -> Sub a
s@(Sub m2) @@ (Sub m1) = Sub $ fmap (apply s) m1 `M.union` m2

empty :: Sub a
empty = Sub M.empty

singleton :: Key t -> t -> Sub t
singleton k v = Sub (M.singleton k v)

delete :: Ord (Key t) => Key t -> Sub t -> Sub t
delete x (Sub m) = Sub (M.delete x m)
---------------------------------

instance Apply Type Type where
  apply (Sub m) t@(TVar (x,_)) = maybe t id (M.lookup x m)
  apply _         (TVal k)     = TVar k
  apply s         (TApp f x)   = TApp (apply s f) (apply s x)

  free (TVar (x,_)) = S.singleton x
  free (TVal _)     = S.empty
  free (TApp f x)   = free f `S.union` free x


instance Apply Kind Kind where
  apply (Sub m) t@(KVar k)   = maybe t id (M.lookup k m)
  apply _         (KVal k)   = KVar k
  apply s         (KArr f x) = KArr (apply s f) (apply s x)

  free (KVar k)   = S.singleton k
  free (KVal _)   = S.empty
  free (KArr f x) = free f `S.union` free x


instance Apply Type Poly where
  apply s (Poly vs t) = Poly vs (apply s' t)
    where s' = foldr delete s (map fst vs)

  free (Poly vs t) = free t S.\\ S.fromList (map fst vs)


instance (Apply t a) => Apply t (Env a) where
  apply s (Env m) = Env (fmap (apply s) m)

  free (Env m) = S.unions $ (fmap free (M.elems m))

----------------

toKindEnv :: Env Poly -> Env Kind
toKindEnv m = fmap p2k m where
  p2k (Poly vs _) = foldr (KArr . snd) (KVal "*") vs


generalize :: Monad m => Env Poly -> Type -> m Poly
generalize env t = do
    let ftv = S.toList (free t S.\\ free env)
    (s,_) <- kindInfer (toKindEnv env) t
    let vs = map (\x -> (x, apply s (KVar x))) ftv
    pure $ Poly vs t


fresh :: Monad m => Kind -> m Type
fresh = undefined


specialize :: Monad m => Poly -> m Type
specialize (Poly vs t) = do
  kts <- flip traverse vs $ \(x,k) -> do
    v <- fresh k
    pure (x,v)
  let s = (Sub . M.fromList) $ kts
  pure (apply s t)


kindInfer :: Monad m => Env Kind -> Type -> m (Sub Kind, Kind)
kindInfer = undefined






