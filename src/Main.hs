{-# Options_GHC  -fmax-relevant-binds=20 #-}
{-# Language TupleSections #-}
{-# Language DeriveFunctor, GeneralizedNewtypeDeriving #-}
module Main where

import Prelude hiding (not, (&&), (||))

import qualified Data.List as L
import           Data.Function (on)


import Errors 
import qualified Parser2 as P
import qualified Infer   as I
import qualified Eval    as Ev
import qualified Env     as En
import qualified Expr    as Ex
import qualified KindInfer as KI


import qualified Control.Monad.Except as E
import qualified Control.Monad.State  as S

import qualified System.IO as IO


import qualified Data.Map as M
import qualified Data.Set as St



main :: IO ()
main = do
  s <- getLine
  runProgram $ runString s
  putStrLn "-------------------"


newtype Program m a = Program { getProgram :: E.ExceptT [ProgramError] m a }
  deriving ( Functor , Applicative, Monad
           , E.MonadError [ProgramError]
           , E.MonadIO
           , E.MonadTrans
           )

runProgram :: Program m a -> m (Either [ProgramError] a)
runProgram = E.runExceptT . getProgram

toProgram :: Monad m => m (Either [ProgramError] a) -> Program m a
toProgram = Program . E.ExceptT


runString :: String -> Program IO ()
runString code = do
  (_,_,e) <- toProgram $ P.runParserT P.defaultPSt code P.expr
  (t,_) <- toProgram $ I.runEval (I.inference e)
  r <- Program $ Ev.eval En.empty e
  E.liftIO (print r)


runFile :: String -> Program IO ()
runFile file = do
  code <- E.liftIO $ IO.getContents
  runString code


-------------------------------------------------------
evalStmt :: En.Env -> I.TypeEnv -> Ex.Statement
         -> Program IO (En.Env, I.TypeEnv)
evalStmt eEnv tEnv d = case d of
  Ex.TypeDef name args body -> do
    (_,args',body') <- addTypeDef2KEnv (toKindEnv tEnv) args body
    let t = foldr (Ex.TApp . Ex.TVar) body' args'
    let tEnv' = I.append name t tEnv
    pure (eEnv,tEnv')


  Ex.LetDef name body -> do
    (t,_) <- toProgram $ I.runEval $ I.ti tEnv body

    (r,t') <-
        if name == "main" then  do
          t' <- pure $ Ex.TArr (Ex.TVal ("unit",Ex.KStar)) t 
          r  <- Program $ Ev.eval eEnv $ Ex.EAbs "_" body
          pure (r,t')
        else do
          t' <- pure t
          r <- Program $ Ev.eval eEnv $ body
          pure (r,t')

    let tEnv' = I.append name t' tEnv
    let eEnv' = En.insert name r eEnv
    pure (eEnv', tEnv')


runSourceFile :: String -> Program IO ()
runSourceFile file = do
    handle <- E.liftIO $ IO.openFile file IO.ReadMode

    code <- E.liftIO $ IO.hGetContents handle

    (_,_,stmts) <- toProgram $ P.runParserT P.defaultPSt code P.program

    (eEnv,tEnv) <- foldrM  stmts $ \st d -> do
      (eEnv,tEnv) <- st
      evalStmt eEnv tEnv d

    case En.find "main" eEnv of
      Nothing -> E.liftIO $ putStrLn "no main defined"
      Just (En.RAbs _ _ e) -> do
        r <- Program $ Ev.eval eEnv $ Ex.EApp (Ex.EAbs "_" e) (Ex.EVal Ex.Unit)
        E.liftIO $ print r

    E.liftIO $ IO.hClose handle
  where
    foldrM xs f = L.foldl' f (pure $ (En.empty,I.emptyEnv)) xs
    


-------------------------------------------------------

-- ex) toKindEnv({... x=t^r -> t^* -> t^* ..}) => {... x=r -> * -> * ...}
toKindEnv :: I.TypeEnv -> KI.KindEnv
toKindEnv (I.TypeEnv m) = KI.KindEnv (toKind <$> m)
  where toKind (I.Poly vs t) = foldr (Ex.KArr . snd) Ex.KStar vs


-- returns (s,s[args],s[type]), s: normalized Kind Sub
addTypeDef2KEnv :: KI.KindEnv -> [Ex.TType] -> Ex.Type 
                -> Program IO (KI.Sub,[Ex.TType],Ex.Type)
addTypeDef2KEnv kenv ftv t0 = do
    let t1 = normalizeKinds kenv t0
    ((_,s1),_) <- toProgram $ KI.runEval (KI.infer kenv t1)
    let t2 = applyDefault s1 t1
    let ftv2 = fmap (apply2Name s1 . fst) ftv
    pure (s1,ftv2,t2)
  where
    apply2Name :: KI.Sub -> Ex.Name -> Ex.TType
    apply2Name s x = (x, KI.apply s (Ex.KVar x))


    applyDefault :: KI.Sub -> Ex.Type -> Ex.Type
    applyDefault ks0 t = I.apply (defKs t) t where
      defKs = I.Sub
            . M.fromList
            . map (\k@(x,_) -> (k,Ex.TVar $ apply2Name ks0 x))
            . St.toList
            . I.free


    normalizeKinds :: KI.KindEnv -> Ex.Type -> Ex.Type
    normalizeKinds kenv = I.apply <$> norm <*> id where
      norm = I.Sub 
           . M.fromList
           . concatMap (\xs@(x:_) -> map (normalize x) xs)
           . L.groupBy ((==) `on` fst)
           . filter (\(x,_) -> x `notElem` KI.free kenv)
           . St.toList 
           . I.free

      normalize x y@(n,_) = case M.lookup n (KI.unKindEnv kenv) of
        Nothing -> (y, Ex.TVar x)
        Just k  -> (y, Ex.TVal (n,k))

  
