module Parse (parseProgram, parseEnv) where
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
          <?> "function declaration"

exprEof = do whiteSpace lx
             e <- expr
             eof
             return e

expr   = arExpr <|> simpleExpr

simpleExpr =    parExpr
            <|> try numExpr
            <|> try ifExpr
            <|> try callExpr
            <|> varExpr

parExpr = parens lx expr <?> "parenthesised expression"

ifExpr = do reserved lx "if"
            p <- expr
            reserved lx "then"
            t <- expr
            reserved lx "else"
            e <- expr
            reserved lx "fi"
            return (If p t e)
         <?> "if-then-else-fi expression"

callExpr = do f <- identifier lx
              args <- parens lx (commaSep1 lx expr)
              return (Call f args)
           <?> "function call"

numExpr = do n <- natural lx
             return (Num n)
          <?> "natural number"

varExpr = do v <- identifier lx
             return (Var v)
          <?> "variable"

-- priorities according to specs;)
table = [[op "*" Mult,op "/" Div],
         [op "+" Plus,op "-" Monus]]
        where op s f = Infix (reservedOp lx s >> return f) AssocLeft

arExpr = buildExpressionParser table simpleExpr <?> "arithmetic expression"


parseProgram :: String -> Either String Expr
parseProgram s = case parse exprEof "expression" s of
                      Left err     -> Left (show err)
                      Right result -> Right result

parseEnv :: String -> Either String Env
parseEnv s = case parse envExpr "environment" s of
                  Left err     -> Left (show err)
                  Right result -> Right result
