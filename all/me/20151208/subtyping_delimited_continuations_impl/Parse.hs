{-# OPTIONS_GHC -fglasgow-exts #-}
module Parse(pr) where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

import Control.Monad
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Maybe
import Data.Char

import Lang

ldef = LanguageDef {
    commentStart = "/*",
    commentEnd = "*/",
    commentLine = "//",
    nestedComments = True,
    identStart = letter <|> char '_',
    identLetter = alphaNum <|> char '_',
    opStart = oneOf "@\\|+*/-=%",
    opLetter = oneOf "-+*/<>=",
    reservedNames = ["case","if","then","else","fix","reset","int","let","in"],
    reservedOpNames = ["@","\\",".","|","->","=","==","<",">",">=","<=","/=","+","-","*","/"],
    caseSensitive = True }

p = makeTokenParser ldef

data St = St { depth :: Int, bvars :: Map String Int }

extend v m = do
    s <- getState
    setState $ s { depth = depth s + 1, bvars = Map.insert v (depth s + 1) (bvars s) }
    r <- m
    setState s
    return r

lookupVar v = do
    m <- Map.lookup v `fmap` (bvars `fmap` getState)
    d <- depth `fmap` getState
    return $ (d-) `fmap` m

varIdentifier p = try $ do
    i <- identifier p
    guard $ isLower $ head i
    return i

consIdentifier p = try $ do
    i <- identifier p
    guard $ isUpper $ head i
    return i

pipeSep p pr = sepBy pr (reservedOp p "|")
pipeSep1 p pr = sepBy1 pr (reservedOp p "|")

prTerm = prExpr
    <|> do
        reservedOp p "\\" 
        v <- varIdentifier p
        dot p
        e <- extend v prTerm
        return $ Lam v e
    <|> do
        reservedOp p "@" 
        v <- varIdentifier p
        dot p 
        e <- extend v prTerm
        return $ Sft v e
    <|> do
        reserved p "fix"
        v <- varIdentifier p
        dot p 
        e <- extend v prTerm
        return $ Fix v e

binaryOp s = reservedOp p s >> return (\x y -> Var (FVar s) `App` x `App` y)
unaryOp s = reservedOp p s >> return (\x -> Var (FVar s) `App` x)

opTable = [
    [Prefix (unaryOp "-")],
    [Infix (binaryOp "*") AssocLeft,
     Infix (binaryOp "/") AssocLeft],
    [Infix (binaryOp "+") AssocLeft,
     Infix (binaryOp "-") AssocLeft],
    [Infix (binaryOp "==") AssocNone,
     Infix (binaryOp "/=") AssocNone,
     Infix (binaryOp "%<=") AssocNone,
     Infix (binaryOp "%>=") AssocNone,
     Infix (binaryOp "%<") AssocNone,
     Infix (binaryOp "%>") AssocNone]]

prExpr = buildExpressionParser opTable prApp

prApp = foldl1 App `fmap` many1 prAtom
        
prAtom = Rst `fmap` angles p prTerm
    <|> do
        es <- parens p $ commaSep p prTerm
        case length es of
            0 -> return $ Cons "Unit" []
            1 -> return $ head es
            k -> return $ Cons ("Tuple" ++ show k) es
    <|> do
        i <- varIdentifier p
        m <- lookupVar i
        return $ Var $ maybe (FVar i) BVar m
    <|> do
        i <- consIdentifier p
        ps <- option [] $ parens p $ commaSep1 p prTerm
        return $ Cons i ps
    <|> do
        k <- natural p
        return $ IntLit k
    <|> do
        reserved p "case"
        e <- prTerm
        es <- braces p $ pipeSep1 p $ do
            i <- consIdentifier p
            ps <- option [] $ parens p $ commaSep1 p $ varIdentifier p
            reservedOp p "->"
            e' <- foldr (.) id (map extend ps) $ prTerm
            return $ (i, ps, e')
        return $ Case e es
    <|> do
        reserved p "if"
        e <- prTerm
        reserved p "then"
        e1 <- prTerm
        reserved p "else"
        e2 <- prTerm
        return $ Case e [("True",[],e1),("False",[],e2)]
    <|> do
        reserved p "let"
        v <- varIdentifier p
        reservedOp p "="
        t <- extend v $ prTerm
        reserved p "in"
        t2 <- extend v $ prTerm
        return $ Lam v t2 `App` Fix v t -- for now, syntactic sugar
    <|> do
        es <- brackets p $ commaSep p prTerm
        return $ foldr (\a b -> Cons "Cons" [a,b]) (Cons "Nil" []) es
{-
prT = do
    t1 <- prTa
    ts <- many $ reservedOp p "->" >> prTa
    case ts of
        [] -> return t1
        _ -> do
            tc <- prTC

prTa = parens p prT
    <|> do
        reserved p "int"
        return TInt
    <|> do
        i <- varIdentifier p
        return $ TVar i
    <|> do
        x <- consIdentifier p
        ts <- many prT
        return $ TADT x ts

prTC = do
        tr1 <- brackets p prTR
        tr2 <- prTR
        return $ tr1 `Chg` tr2
    <|> return Ind

prTR = do
    t <- prT
    tc <- prTC
    return (t,tc)
-}
pr = runParser prTerm (St 0 Map.empty) ""

