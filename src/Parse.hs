{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse ( stm, Parse.parse, decl, runP, P, program, declOrTm ) where

import Prelude hiding ( const )
import Lang
import Common
import Text.Parsec hiding (runP,parse)
import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser $
        emptyDef {
         commentLine    = "#",
         reservedNames = ["let","fun","fix","then","else","in",
                           "ifz","print","Nat","rec","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> (do ty <- var
                 return (SDecTy ty))
         <|> parens typeP

typeP :: P STy
typeP = try (do
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  (do a <- atom
      return (SPrint i str a)
    <|> return (SUnPrint i str))

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table stm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, STy)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v,ty)

multibinding :: P ([Name], STy)
multibinding = do vs <- many1 var
                  reservedOp ":"
                  ty <- typeP
                  return (vs,ty)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         args <- many (parens multibinding)
         reservedOp "->"
         t <- expr
         return (SLam i args t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = (do i <- getPos
          f <- atom
          args <- many atom
          return (foldl (SApp i) f args))

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f,fty) <- parens binding
         args <- many (parens multibinding)
         reservedOp "->"
         t <- expr
         return (SFix i f fty args t)

rec :: P Bool
rec = do reserved "rec"
         return True
     <|> return False

letbindings :: P (Name, [([Name], STy)], STy)
letbindings = do f <- var
                 args <- many (parens multibinding)
                 reservedOp ":"
                 ty <- typeP
                 return (f,args,ty)
             <|> do (v,ty) <- binding
                    return (v,[],ty)

letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  r <- rec
  (v,args,ty) <- parens letbindings <|> letbindings
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i r v args ty def body)

-- | Parser de términos
stm :: P STerm
stm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

-- | Parsers de declaraciones
typeDecl :: P SDecl
typeDecl = do i <- getPos
              reserved "type"
              n <- var
              reservedOp "="
              ty <- typeP
              return (STypeDecl i n ty)

sdecl :: P SDecl
sdecl = do
      i <- getPos
      reserved "let"
      r <- rec
      (v,args,ty) <- parens letbindings <|> letbindings
      reservedOp "="
      t <- expr
      return (SDecl i r v args ty t)

decl :: P SDecl
decl = typeDecl <|> sdecl

-- | Parser de programas (listas de declaraciones)
program :: P [SDecl]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either SDecl STerm)
declOrTm =  try (Right <$> expr) <|> (Left <$> decl)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> Either SDecl STerm
parse s = case runP declOrTm s "" of
            Right t -> t
            Left e  -> error ("no parse: " ++ show s)
