module Main where
-- $Id$

-- $ runhaskell  Main.hs soubor_s_definicemi "vyraz na vyhodnoceni"
-- $ runhugs -98 Main hs soubor_s_definicemi "vyraz na vyhodnoceni"

import System.Environment

import Parse
import Expr

main :: IO ()
main = do args <- getArgs
          progname <- getProgName
          if length args < 1 || length args > 2
            then printUsage progname
            else do defs <- (readFile (args!!0))
                    case parseEnv defs of
                      Left s  -> putStrLn ("Parse error: " ++ s)
                      Right e -> checkDefsAndRun args e

printUsage pname = putStrLn ("usage: " ++ pname ++ " <declarations-file> [expression]\n\n" ++
                             "loads declarations from <declarations-file> and evaluates expression\n" ++
                             "if given, otherwise reads expressions from standard input")

-- zkontroluje prostredi a pokud je ok, vyhodnoti program
checkDefsAndRun :: [String] -> Env -> IO ()
checkDefsAndRun args env = do case checkDefs env of
                                Just err -> putStrLn err
                                Nothing  -> do putStrLn ("Loaded " ++ show (length env) ++ " functions\n")
                                               if length args == 1
                                                 then runStdIn env
                                                 else runCmdLine env (args!!1)

checkDefs :: Env -> Maybe String
checkDefs e = if not $ null fvo
                then Just ("Error: following functions contain free variable:\n" ++ stringify fvo)
                else if not $ null udc
                       then Just ("Error: in function " ++ (fst.head) udc ++
                                  ": call to undefined function " ++ (snd.head) udc ++ "\n")
                       else if not $ null amm
                              then Just ("Error: in function " ++ (fst.head) amm ++
                                         ": call to " ++ (snd.head) amm ++ " with wrong number of arguments\n")
                              else Nothing
              where udc = [(funName fun,callto) | fun<-e, (callto,_)<-(calls fun), callto `notElem` (map funName e)]
                    fvo = [(funName fun,fvars) | fun<-e, let fvars = freeVars fun, not $ null fvars ]
                    amm = [(funName fun,callto) | fun<-e, (callto,num)<-(calls fun), num /= arity e callto]
                    stringify = unlines . map (\(n,fvs) -> n ++ " (variables: " ++ (parmlist fvs) ++ ")")

checkProgram :: Env -> Expr -> Maybe String
checkProgram env e = if not $ null fv
                       then Just ("Error: program contains variable: " ++ head fv ++ "\n")
                       else if not $ null udc
                              then Just ("Error: call to undefined function " ++ head udc ++ "\n")
                              else if not $ null amm
                                     then Just ("Error: call to " ++ head amm ++ " with wrong number of arguments\n")
                                     else Nothing
                     where fv = freeVars pseudofun
                           udc = [callto | (callto,_)<-(calls pseudofun), callto `notElem` (map funName env)]
                           amm = [callto | (callto,num)<-(calls pseudofun), num /= arity env callto]
                           pseudofun = Function undefined [] e

arity :: Env -> String -> Int
arity ((Function n a _):xs) str = if n == str then length a else arity xs str


runCmdLine :: Env -> String -> IO ()
runCmdLine e s = putStrLn $ evalStr e s

runStdIn :: Env -> IO ()
runStdIn e = interact (unlines.map (evalStr e).map checkExit.lines)
            where checkExit s = case s of -- ugly, ugly, ugly, ugly ...
                                  "quit" -> error "quit"
                                  "exit" -> error "quit"
                                  _      -> s


evalStr :: Env -> String -> String
evalStr env s = case parseProgram s of
                 Left err -> "Parse error: " ++ err
                 Right e  -> case checkProgram env e of
                               Just err -> err
                               Nothing  -> scan env e

testExpr = (If (Monus (Num 2) (Num 4)) (Call "fun" [(Num 42),(If (Num 666) (Var "var") (Num 0))]) (Div (Num 1) (Num 0)))
goodFun = Function "good" ["x","y","z"] (If (Var "x") (Var "y") (Plus (Num 42) (Var "z")))
baadFun = Function "baad" ["z"] (If (Var "x") (Var "y") (Plus (Num 42) (Var "z")))
testInfix = Mult (Plus (Num 1) (Num 2)) (Monus (Num 3) (Num 4))
