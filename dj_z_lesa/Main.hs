module Main where

import Parse
import Expr

run envStr exprStr = do let env = parseEnv envStr
                            prg = parseProgram exprStr
                        print env
                        print prg
                        print (eval env prg)

testExpr = (If (Monus (Num 2) (Num 4)) (Call "fun" [(Num 42),(If (Num 666) (Var "var") (Num 0))]) (Div (Num 1) (Num 0)))

goodFun = Function "good" ["x","y","z"] (If (Var "x") (Var "y") (Plus (Num 42) (Var "z")))

baadFun = Function "gaad" ["z"] (If (Var "x") (Var "y") (Plus (Num 42) (Var "z")))
