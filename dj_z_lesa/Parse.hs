module Parse where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language (emptyDef)

import Expr

lexer = makeTokenParser (emptyDef
                         {reservedOpNames = ["*","/","+","-","="],
                          reservedNames = ["if","then","else","fi"]})

envExpr = do whiteSpace lexer
             funs <- many funDecl
             eof
             return funs

funDecl = do funname <- identifier lexer
             args <- parens lexer (commaSep1 lexer (identifier lexer))
             reservedOp lexer "="
             body <- expr
             return (Function funname args body)

exprEof = do whiteSpace lexer
             e <- expr
             eof
             return e

expr   = arExpr <|> factor
factor = parens lexer expr <|> try numExpr <|> try ifExpr <|> try callExpr <|> varExpr

ifExpr = do reserved lexer "if"
            p <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            reserved lexer "fi"
            return (If p t e)

callExpr = do f <- identifier lexer
              args <- parens lexer (commaSep1 lexer expr)
              return (Call f args)

numExpr = do n <- natural lexer
             return (Num n)

varExpr = do v <- identifier lexer
             return (Var v)

table = [[op "*" Mult],[op "/" Div],
         [op "+" Plus],[op "-" Monus]]
        where op s f = Infix (reservedOp lexer s >> return f) AssocLeft

arExpr = buildExpressionParser table factor


spaces1 = skipMany1 space

parseProgram :: String -> Expr
parseProgram s = case parse exprEof "expression" s of
                      Left err     -> error $ "Error:\n" ++ show err
                      Right result -> result

parseEnv :: String -> [Function]
parseEnv s = case parse envExpr "environment" s of
                  Left err -> error $ "Error:\n" ++ show err
                  Right result -> result
