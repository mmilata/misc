module Parse where

import Text.ParserCombinators.Parsec

import Expr

envExpr = many funDecl

funDecl = do funname <- many1 letter
             char '('
             args <- (many1 letter) `sepBy1` (char ',')
             char ')'
             char '='
             body <- expr
             return (Function funname args body)

expr = (try callExpr) <|> (try ifExpr) <|> arExpr

callExpr = do funname <- many1 letter
              char '('
              args <- expr `sepBy1` (char ',')
              char ')'
              return (Call funname args)

ifExpr = do string "if "
            cond <- expr
            string " then "
            thenE <- expr
            string " else "
            elseE <- expr
            string " fi"
            return (If cond thenE elseE)

arExpr  = divExpr `chainl1` (char '/' >> return Div)
divExpr = mulExpr `chainl1` (char '*' >> return Mult)
mulExpr = monExpr `chainl1` (char '-' >> return Monus)
monExpr = plusExpr `chainl1` (char '+' >> return Plus)
plusExpr = parenExpr <|> numExpr <|> varExpr

parenExpr = do char '('
               e <- expr
               char ')'
               return e

numExpr = do n <- many1 digit
             return (Num (read n))

varExpr = do varname <- many1 letter
             return (Var varname)

parseProgram :: String -> Expr
parseProgram s = case parse expr "expression" s of
                      Left err     -> error $ "Error:\n" ++ show err
                      Right result -> result

parseEnv :: String -> [Function]
parseEnv s = case parse envExpr "environment" s of
                  Left err -> error $ "Error:\n" ++ show err
                  Right result -> result
