module Main where
-- $Id$

-- $ runhaskell  Main.hs soubor_s_definicemi "vyraz na vyhodnoceni"
-- $ runhugs -98 Main hs soubor_s_definicemi "vyraz na vyhodnoceni"

import System.Environment

import Parse
import Expr

main :: IO ()
main = do args <- getArgs
          prog <- getProgName
          if length args /= 2
             then printUsage prog
             else do definitions <- (readFile (args!!0))
                     run definitions (args!!1)

printUsage pname = putStrLn ("Usage: " ++ pname ++ " declarations_file expression\n\n" ++
                             "loads declarations from the file and evaluates expression")


run envStr exprStr = do let env = parseEnv envStr
                            prg = parseProgram exprStr
                        if any (not.checkFunction) env
                           then error "Some definition contains free variable"
                           else do putStrLn $ "Environment:\n" ++ unlines (map fToStr env)
                                   putStrLn $ "Expression: " ++ toStr prg ++ "\n"
                                   putStrLn (scan env prg)

test envStr exprStr = do let env = parseEnv envStr
                             prg = parseProgram exprStr
                         print env
                         print prg
                         print (eval env prg)

testExpr = (If (Monus (Num 2) (Num 4)) (Call "fun" [(Num 42),(If (Num 666) (Var "var") (Num 0))]) (Div (Num 1) (Num 0)))
goodFun = Function "good" ["x","y","z"] (If (Var "x") (Var "y") (Plus (Num 42) (Var "z")))
baadFun = Function "baad" ["z"] (If (Var "x") (Var "y") (Plus (Num 42) (Var "z")))
testInfix = Mult (Plus (Num 1) (Num 2)) (Monus (Num 3) (Num 4))
