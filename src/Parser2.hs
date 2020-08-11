{-# Language DeriveFunctor #-}
{-# Language ScopedTypeVariables #-}
{-# Language LambdaCase #-}
module Parser2 where

import Control.Applicative
import Expr
import Errors

import qualified Control.Monad.Except as E
import qualified Control.Monad.State as S

isNewLine :: Char -> Bool
isNewLine c = 
  [c] `elem` ["\r","\n","\r\n"]

incPos :: Char -> PSt -> PSt
incPos x (PSt (r,c) s g)
    | isNewLine x = PSt (r + 1,0) s g
    | otherwise   = PSt (r,c + 1) s g

-----------------------------------------------
data PSt = PSt { pstPos :: Pos
               , pstCount :: Int
               , varGen :: Int
               }
  deriving (Eq,Show)

defaultPSt :: PSt
defaultPSt = PSt (0,0) 0 0

newtype ParserT m a = ParserT { 
      getParserT :: (PSt,String) -> E.ExceptT [ProgramError] m (PSt,String,a) 
    }
  deriving Functor

runParserT :: Monad m 
          => PSt -> String -> ParserT m a 
          -> m (Either [ProgramError] (PSt ,String,a))
runParserT pos src p = E.runExceptT $ getParserT p (pos,src)



instance Monad m => Applicative (ParserT m) where
  pure x = ParserT $ \(p,s) -> E.ExceptT . pure $ Right (p,s,x)

  pF <*> pX = ParserT $ \(p,s) -> E.ExceptT $ do
    resF <- runParserT p s pF
    case resF of
      Left err1 -> pure (Left err1)

      Right (p',s',f) -> do
        resX <- runParserT p' s' pX

        case resX of
          Left err2 -> pure (Left err2)

          Right (p'',s'',x) -> pure $ Right (p'',s'',f x)


instance Monad m => Alternative (ParserT m) where
  empty = ParserT $ \(p,_) -> 
    E.ExceptT $ pure $ Left [parseError (pstPos p) "parse failed"]

  pA <|> pB = ParserT $ \(p,s) -> do
    resA <- E.lift $ runParserT p s pA
    case resA of
      Right suc -> E.ExceptT $ pure (Right suc)
      Left err1 -> do
        resB <- E.lift $ runParserT p s pB
        case resB of
          Right suc -> E.ExceptT $ pure (Right suc)
          Left err2 -> E.ExceptT $ pure (Left $ err1 ++ err2)
            

instance Monad m => Monad (ParserT m) where
  pm >>= f = ParserT $ \(p,s) -> E.ExceptT $ do
      resP <- runParserT p s pm
      case resP of
        Left err -> pure (Left err)
        Right (p',s',x) -> runParserT p' s' (f x)


instance E.MonadTrans ParserT where
    lift m = ParserT $ \(p,s) -> E.ExceptT $ fmap (\x -> Right (p,s,x)) m

-------------------------------------------------------------------------
getPSt :: Monad m => ParserT m PSt
getPSt = ParserT $ \(pst,s) ->
  E.ExceptT . pure $ Right (pst,s,pst)


setPSt :: Monad m => PSt -> ParserT m ()
setPSt pst = ParserT $ \(_,s) ->
  E.ExceptT . pure $ Right (pst,s,())


modifyPSt :: Monad m => (PSt -> PSt) -> ParserT m ()
modifyPSt f = 
  getPSt >>= setPSt . f


freshVar :: Monad m => Name -> ParserT m Kind
freshVar prefix = do
  p <- getPSt
  let i = varGen p
  setPSt $ p{varGen = 1 + i}
  pure $ KVar (prefix ++ show i)

-------------------------------------------------


parseFail :: Monad m => String -> ParserT m a
parseFail msg = ParserT $ \(p,s) -> 
    E.ExceptT . pure $ Left [parseError (pstPos p) msg]


recoverWith :: Monad m => ParserT m a -> ([ProgramError] -> ParserT m a) -> ParserT m a
recoverWith pm f = ParserT $ \(p,s) -> E.ExceptT $ do
  x <- runParserT p s pm
  case x of
    Left err  -> runParserT p s (f err)
    Right suc -> pure (Right suc)


------------------------------------------------------------------------
testChar :: Monad m => (Char -> Bool) -> ParserT m Char
testChar f = ParserT $ \(p,s) -> E.ExceptT $ case s of
  c : cs 
    | f c       -> pure $ Right (incPos c p,cs, c)
    | otherwise ->
        pure $ Left [parseError (pstPos p) $ "unexpected character `" ++ [c] ++ "`"]

  []            -> 
        pure $ Left [parseError (pstPos p) $ "unexpected EOF"]


neg :: Monad m => ParserT m a -> ParserT m ()
neg p = ParserT $ \(pst,s) -> E.ExceptT $ do
    resP <- runParserT pst s p
    case resP of
      Left _ -> pure $ Right (pst,s,())
      Right _ -> pure $ Left [parseError (pstPos pst) "neg lookahead failed"]


peek :: Monad m => ParserT m a -> ParserT m a
peek p = ParserT $ \(pst,s) -> E.ExceptT $ do
    resP <- runParserT pst s p
    case resP of
      Right (_,_,x) -> pure $ Right (pst,s,x)
      Left err -> pure $ Left (parseError (pstPos pst) "pos lookahead failed" : err)

--------------------------------------------------------------------------
alts :: Alternative f => [f a] -> f a
alts []     = empty
alts (x:xs) = x <|> alts xs
----------
named :: Monad m => String -> ParserT m a -> ParserT m a
named ident p = p `recoverWith` \_ -> parseFail ident

p <?> m = named m p

------------
char :: Monad m => Char -> ParserT m Char
char c = testChar (== c) <?> ("expected: " ++ [c])

anyChar :: Monad m => ParserT m Char
anyChar = testChar (const True)

endOfFile :: Monad m => ParserT m ()
endOfFile = neg anyChar


oneOf :: Monad m => String -> ParserT m Char
oneOf elems = testChar (`elem` elems) <?> ("expected one of: " ++ elems)


string :: Monad m => String -> ParserT m String
string s = traverse char s <?> ("expected " ++ s)


orElse :: Monad m => a -> ParserT m a -> ParserT m a 
orElse zero p = p <|> pure zero
------------------------------------------------------------------------

space :: Monad m => ParserT m ()
space = many (newline <|> whitespace) *> pure () <?> "space"
  where
    newline    = (string "\n" <|> string "\r" <|> string "\r\n") *> pure ()
    whitespace = oneOf " \t" *> pure ()


token :: Monad m => ParserT m a -> ParserT m a
token p = p <* space


symbol :: Monad m => String -> ParserT m ()
symbol s = token (string s) *> pure () <?> ("symbol: " ++ s)


digit :: Monad m => ParserT m Char
digit = oneOf ['0'..'9'] <?> "digit"


int :: Monad m => ParserT m Int
int = named "int" $ token $ do
  sign <- orElse ' ' (char '-')
  digits <- some digit
  pure $ read (sign : digits)


bool :: Monad  m => ParserT m Bool
bool = (true <|> false) <?> "bool"
  where
    true  = symbol "true"  *> pure True
    false = symbol "false" *> pure False


identifier :: Monad m => ParserT m String
identifier = named "identifier" $ token $ 
    (:) <$> identStart <*> many identPart
  where
    identStart = char '_' <|> oneOf ['a'..'z']
    identPart = identStart <|> oneOf ['A'..'Z'] <|> digit


between :: Monad m => ParserT m open -> ParserT m close -> ParserT m a -> ParserT m a 
between open close p = open *> p <* close

betweenS :: Monad m => String -> String -> ParserT m a -> ParserT m a 
betweenS o c = between (symbol o) (symbol c)

parens :: Monad m => ParserT m a -> ParserT m a 
parens = betweenS "(" ")"


sepBy :: Monad m => ParserT m sep -> ParserT m a -> ParserT m [a]
sepBy s a = reverse <$> loop []
  where
    loop k = orElse k $ do
      x <- a
      let k' = x : k
      orElse k' (s *> loop k')

---------------------------------------------------------------------
pattern :: Monad m => ParserT m Pattern
pattern =  (symbol "_" *> pure PEmpty)
       <|> ((PVal . I) <$> int)
       <|> ((PVal . B) <$> bool)
       <|> (PVar <$> var <* neg (symbol "@"))
       <|> (PAs <$> (var <* symbol "@") <*> pattern)
       <|> (parens pattern)
       <|> (betweenS "<" ">" patAlt)
       <|> (betweenS "{" "}" patRec)


patAlt :: Monad m => ParserT m Pattern
patAlt = PAlt <$> identifier <*> (symbol "=" *> pattern) 


patRec :: Monad m => ParserT m Pattern
patRec = PRec <$> sepBy (symbol "|") assign
  where
    assign = (,) <$> identifier <*> (symbol "=" *> pattern) 


patCase :: Monad m => ParserT m (Pattern,Expr)
patCase = do
  symbol "|"
  p <- pattern
  symbol "->"
  e <- expr
  pure (p,e)
---------------------------------------------------------------------

reservedWords :: [String]
reservedWords = ["if","then","else","let","in","lam","match","end","true","false"]


var :: Monad m => ParserT m String
var = named "var" $ do
  x <- identifier
  guard (x `notElem` reservedWords)
  pure x


expr :: Monad m => ParserT m Expr
expr = prefix <|> opPrec 


prefix :: Monad m => ParserT m Expr
prefix =  (ELet <$> (symbol "let" *> var) 
                <*> (absP "=" <|> (symbol "=" *> expr))
                <*> (symbol "in"  *> expr))
  
      <|> (ECond <$> (symbol "if"   *> expr)
                 <*> (symbol "then" *> expr)
                 <*> (symbol "else" *> expr))

      <|> (symbol "lam" *> absP ".")

      <|> (EMatch <$> (symbol "match" *> expr)
                  <*> (some patCase) 
                  <*   symbol "end")


opPrec :: Monad m => ParserT m Expr
opPrec = mkOpPrecParserT term
    [ Infix   5  NonAssoc   (symbol "<=" *> pure ELEq)
    , Infix   6  AssocRight (symbol "+" *> pure EAdd)
    , Infix   7  AssocRight (symbol "*" *> pure EMul)
    , Infix  10  AssocLeft  funApp
    , Suffix 11             (suffix "."  ERecSel)
    , Suffix 11             (suffix "//" ERecRem)
    ] 
  where
    funApp = do
      neg (symbol "." <|> symbol "//")
      peek term
      pure EApp

    suffix sym fun = do
      symbol sym
      l <- identifier
      pure (\e -> fun e l)


term :: Monad m => ParserT m Expr
term =  ((EVal . I) <$> int)
    <|> ((EVal . B) <$> bool)
    <|> (symbol "()" *> pure (EVal Unit))
    <|> (EVar <$> var)
    <|> (parens expr)
    <|> (betweenS "<" ">" altP)
    <|> (betweenS "{" "}" recP)
    <|> (symbol "{}" *> pure (ERecEmpty))
    <|> (symbol "<>" *> pure (EAltEmpty))


recP :: Monad m => ParserT m Expr
recP = do
  l <- identifier
  symbol "="
  e <- expr
  r <- orElse ERecEmpty $ do
    symbol "|" 
    recP <|> expr
  pure $ ERecExt l e r


altP :: Monad m => ParserT m Expr
altP = identifier >>= ((<|>) <$> inj <*> emb)
{-
altP = do
    l <- identifier
    inj l <|> emb l
-}
  where
    inj l = do
      symbol "="
      e <- expr
      pure (EInj l e)
    emb l = do
      symbol "|"
      e <- altP <|> expr
      pure (EEmb l e)


absP :: Monad m => String -> ParserT m Expr
absP d = do
    xs <- some var
    symbol d
    e <- expr
    pure $ foldr EAbs e xs


-----------------------------------------------------------------

typeAtom :: ParserT IO Type
typeAtom =  (symbol "int" *> pure (TVal ("int",KStar)) <?> "int")
        <|> (symbol "bool" *> pure (TVal ("bool",KStar)) <?> "bool")
        <|> (symbol "unit" *> pure (TVal ("unit",KStar)) <?> "unit")

        <|> (TRec <$> (symbol "{}" *> pure TRowNull))
        <|> (TRec <$> (betweenS "{" "}" (rowP <|> tVar)))

        <|> (TAlt <$> (symbol "<>" *> pure TRowNull))
        <|> (TAlt <$> (betweenS "<" ">" (rowP <|> tVar)))

        <|> tVar
        <|> (parens typeP)

typeIdent :: ParserT IO String
typeIdent = named "ident" $ do
  ident <- identifier
  guard (ident `notElem` ["let","type"])
  pure ident


tVar :: ParserT IO Type
tVar = named "tvar" $ do
  l <- typeIdent
  pure $ TVar (l, KVar "stub")

typeP :: ParserT IO Type
typeP = mkOpPrecParserT typeAtom
    [ Infix 5  AssocRight (symbol "->" *> pure TArr)
    , Infix 10 AssocLeft  (peek typeAtom *> pure TApp)
    ]

rowP = do
  l <- typeIdent
  symbol ":"
  a <- typeP
  r <- orElse TRowNull $ do
    symbol "|"
    rowP <|> tVar
  pure (TRowExt l a r)

      
----------------------------------------------------------------------
    

statment :: ParserT IO Statement
statment =  (TypeDef <$> (symbol "type" *> typeIdent) 
                     <*> (map (\(TVar x) -> x) <$> some tVar)
                     <*> (symbol "=" *> typeP))

        <|> (LetDef <$> (symbol "let" *> var) 
                    <*> (absP "=" <|> (symbol "=" *> expr)))


program :: ParserT IO [Statement]
program = space *> many (token statment) <* endOfFile


-----------------------------------------------------------------

guard :: Alternative f => Bool -> f ()
guard True  = pure ()
guard False = empty

data Assoc = AssocLeft | AssocRight | NonAssoc
  deriving (Eq, Show)


data OpPrec m a = Infix  Int Assoc (ParserT m (a -> a -> a))
                | Suffix Int       (ParserT m (a -> a))

gopParserT :: Monad m => OpPrec m a -> ParserT m (OpPrec m a)
gopParserT op@(Infix  _ _ p) = p *> pure op
gopParserT op@(Suffix _   p) = p *> pure op

gopPrec (Infix p _ _) = p
gopPrec (Suffix p _)  = p


mkOpPrecParserT :: forall m a . Monad m => ParserT m a -> [OpPrec m a] -> ParserT m a
mkOpPrecParserT atom opTable = atom >>= parseOp 0
  where
    nextOpPrec :: ParserT m (OpPrec m a)
    nextOpPrec = alts $ map gopParserT opTable

    parseOp :: Int -> a -> ParserT m a
    parseOp minPrec lhs = orElse lhs $ do
      op <- peek $ nextOpPrec 
      guard $ gopPrec op >= minPrec
      lhs' <- case op of
        Suffix _ f ->  do
          suffix <- f
          pure (suffix lhs)
        Infix p _ f -> do
          binary <- f
          rhs <- atom >>= loopRight p
          pure (binary lhs rhs)
      parseOp minPrec lhs'


    loopRight :: Int -> a -> ParserT m a
    loopRight opPrec rhs = orElse rhs $ do
      op <- peek nextOpPrec
      p <- case op of
        Suffix p _ -> do
          pure p
        Infix p a _ -> do
          guard (a /= NonAssoc)
          guard $ p > opPrec || (a == AssocRight && p == opPrec)
          pure p
      rhs' <- parseOp p rhs
      loopRight opPrec rhs'


