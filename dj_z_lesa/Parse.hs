module Parse where
-- $Id$

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language (emptyDef)

import Expr

lx = makeTokenParser (emptyDef
                      {reservedOpNames = ["*","/","+","-","="],
                       reservedNames = ["if","then","else","fi"]})

envExpr = do whiteSpace lx
             funs <- many funDecl
             eof
             return funs

funDecl = do funname <- identifier lx
             args <- parens lx (commaSep1 lx (identifier lx))
             reservedOp lx "="
             body <- expr
             return (Function funname args body)

exprEof = do whiteSpace lx
             e <- expr
             eof
             return e

expr   = arExpr <|> factor
factor = parens lx expr <|> try numExpr <|> try ifExpr <|> try callExpr <|> varExpr

ifExpr = do reserved lx "if"
            p <- expr
            reserved lx "then"
            t <- expr
            reserved lx "else"
            e <- expr
            reserved lx "fi"
            return (If p t e)

callExpr = do f <- identifier lx
              args <- parens lx (commaSep1 lx expr)
              return (Call f args)

numExpr = do n <- natural lx
             return (Num n)

varExpr = do v <- identifier lx
             return (Var v)

-- dle specifikace;)
table = [[op "*" Mult,op "/" Div],
         [op "+" Plus,op "-" Monus]]
        where op s f = Infix (reservedOp lx s >> return f) AssocLeft

arExpr = buildExpressionParser table factor


parseProgram :: String -> Either String Expr
parseProgram s = case parse exprEof "expression" s of
                      Left err     -> Left (show err)
                      Right result -> Right result

parseEnv :: String -> Either String Env
parseEnv s = case parse envExpr "environment" s of
                  Left err     -> Left (show err)
                  Right result -> Right result
