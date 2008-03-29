module Parse where

import Text.ParserCombinators.Parsec

import Expr

envExpr = do funs <- many funDecl
             spaces
             eof
             return funs

funDecl = do funname <- many1 letter
             spaces
             char '('
             spaces
             args <- (many1 letter) `sepBy1` (spaces >> char ',' >> spaces)
             spaces
             char ')'
             spaces
             char '='
             spaces
             body <- expr
             return (Function funname args body)

exprEof = do e <- expr
             spaces
             eof
             return e

expr = do spaces
          (try callExpr) <|> (try ifExpr) <|> arExpr

callExpr = do funname <- many1 letter
              char '('
              args <- expr `sepBy1` (char ',')
              char ')'
              return (Call funname args)

ifExpr = do string "if"
            spaces1
            cond <- expr
            spaces1
            string "then"
            spaces1
            thenE <- expr
            spaces1
            string "else"
            spaces1
            elseE <- expr
            spaces1
            string "fi"
            return (If cond thenE elseE)

arExpr   = divExpr `chainl1` (spaces >> char '/' >> return Div)
divExpr  = mulExpr `chainl1` (spaces >> char '*' >> return Mult)
mulExpr  = monExpr `chainl1` (spaces >> char '-' >> return Monus)
monExpr  = plusExpr `chainl1` (spaces >> char '+' >> return Plus)
plusExpr = parenExpr <|> numExpr <|> varExpr

parenExpr = do char '('
               spaces
               e <- expr
               spaces
               char ')'
               return e

numExpr = do spaces
             n <- many1 digit
             return (Num (read n))

varExpr = do varname <- many1 letter
             return (Var varname)

spaces1 = skipMany1 space

parseProgram :: String -> Expr
parseProgram s = case parse exprEof "expression" s of
                      Left err     -> error $ "Error:\n" ++ show err
                      Right result -> result

parseEnv :: String -> [Function]
parseEnv s = case parse envExpr "environment" s of
                  Left err -> error $ "Error:\n" ++ show err
                  Right result -> result
