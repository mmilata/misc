module Expr
   ( Expr(Var, Num, Plus, Monus, Mult, Div, Call, If),
     Function(Function), Env, funName, funArgs, funBody, calls,
     freeVars, parmlist, evalScan, evalScanS, debugShowExpr ) where
-- $Id$

import Data.List
import Data.Maybe

data Expr = Var String
          | Num Integer
          | Plus Expr Expr
          | Monus Expr Expr
          | Mult Expr Expr
          | Div Expr Expr
          | Call String [Expr]
          | If Expr Expr Expr

instance Show Expr where
   show (Num n)     = show n
   show (Var s)     = s
   show (Plus m n)  = infop "+" m n
   show (Monus m n) = infop "-" m n
   show (Mult m n)  = infop' "*" m n
   show (Div m n)   = infop' "/" m n
   show (Call f p)  = f ++ "(" ++ parmlist (map show p) ++ ")"
   show (If p t e)  = "if " ++ show p ++ " then " ++ show t ++ " else " ++ show e ++ " fi"

infop o a b = show a ++ " " ++ o ++ " " ++ show b
infop' o a b = paren a ++ " " ++ o ++ " " ++ paren b
               where paren e@(Plus  _ _) = "(" ++ show e ++ ")"
                     paren e@(Monus _ _) = "(" ++ show e ++ ")"
                     paren e            = show e

debugShowExpr :: Expr -> String
debugShowExpr = foldExpr (\n -> "Num " ++ show n)
                         [ bop "Plus", bop "Minus", bop "Mult", bop "Div" ]
                         (\s -> "Var " ++ s)
                         (\s ar -> "Call " ++ s ++ " " ++ show ar)
                         (\p t e -> "If ("++p++") ("++t++") ("++e++")")
                where bop str a b = str ++ " (" ++ a ++ ") (" ++ b ++ ")"

data Function = Function String [String] Expr

instance Show Function where
   show (Function name args body) = name ++ "(" ++ parmlist args ++ ") = " ++ show body

type Env = [Function]

foldExpr :: (Integer -> a)       -- function on numbers
         -> [a -> a -> a]        -- functions on binary operators
         -> (String -> a)        -- function on variables
         -> (String -> [a] -> a) -- function on calls
         -> (a -> a -> a -> a)   -- function on if
         -> Expr                 -- expression
         -> a
foldExpr f _ _ _ _ (Num n)     = f n
foldExpr l b v c i (Plus m n)  = (b!!0) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr l b v c i (Monus m n) = (b!!1) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr l b v c i (Mult m n)  = (b!!2) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr l b v c i (Div m n)   = (b!!3) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr _ _ v _ _ (Var x)     = v x
foldExpr l b v c i (Call f ar) = c f (map (foldExpr l b v c i) ar)
foldExpr l b v c i (If p t e)  = i (foldExpr l b v c i p) (foldExpr l b v c i t) (foldExpr l b v c i e)

getFunction :: Env -> String -> Function
getFunction env str = case find (\(Function name _ _) -> name == str) env of
                        Nothing -> error "Function not in environment"
                        Just f  -> f

funName :: Function -> String
funName (Function n _ _) = n

funArgs :: Function -> [String]
funArgs (Function _ a _) = a

funBody :: Function -> Expr
funBody (Function _ _ b) = b

reducible :: Expr -> Bool
reducible (Num _) = False
reducible _       = True

freeVars :: Function -> [String]
freeVars (Function _ parms body) = foldExpr (const []) (repeat union)  fv fc fi body
                                   where fc _ args = foldl1 union args
                                         fi p t e  = p `union` t `union` e
                                         fv v      = [v] \\ parms

calls :: Function -> [(String,Int)]
calls (Function _ _ body) = foldExpr (const []) (repeat union) (const []) fc fi body
                            where fc fn args = [(fn,length args)] `union` (foldl1 union args)
                                  fi p t e   = p `union` t `union` e

eval :: Env -> Expr -> Integer
eval env = foldExpr id [(+),monus,(*),mydiv] fv fc fi
            where monus a b = if a-b < 0 then 0 else a-b
                  mydiv a b = if b == 0 then 0 else a `div` b
                  fv v      = error "Free variable"
                  fi p t e  = if p > 0 then t else e
                  fc f a    = eval env (subst (funArgs fun) a (funBody fun))
                              where fun = getFunction env f

step :: Env -> Expr -> Expr
step _   (Num n)     = Num n
step env (Var v)     = error "Free variable"
step env (If p t e)  | reducible p = (If (step env p) t e)
                     | otherwise   = if (eval env p) > 0 then t else e
step env (Call f ar) | all (not.reducible) ar = subst (funArgs fun) (map (eval env) ar) (funBody fun)
                     | otherwise              = (Call f (liststep ar))
                       where fun             = getFunction env f
                             liststep (x:xs) = if reducible x then (step env x):xs else x:(liststep xs)
step env (Monus m n) | reducible m = (Monus (step env m) n)
                     | reducible n = (Monus m (step env n))
                     | otherwise   = Num (eval env (Monus m n))
step env (Plus m n)  | reducible m = (Plus (step env m) n)
                     | reducible n = (Plus m (step env n))
                     | otherwise   = Num (eval env (Plus m n))
step env (Mult m n)  | reducible m = (Mult (step env m) n)
                     | reducible n = (Mult m (step env n))
                     | otherwise   = Num (eval env (Mult m n))
step env (Div m n)   | reducible m = (Div (step env m) n)
                     | reducible n = (Div m (step env n))
                     | otherwise   = Num (eval env (Div m n))

subst :: [String] -> [Integer] -> Expr -> Expr
subst parnames vals e | length vals /= length parnames = error "Arity mismatch"
                      | otherwise                      = subst' (zip parnames vals) e

subst' :: [(String,Integer)] -> Expr -> Expr
subst' vals = foldExpr Num [Plus,Monus,Mult,Div] fv Call If
              where fv v = Num $ fromMaybe (error "Free variable") (lookup v vals)

parmlist :: [String] -> String
parmlist [w]    = w
parmlist (w:ws) = w ++ ',':(parmlist ws)

evalScan :: Env -> Expr -> [Expr]
evalScan env expr | reducible expr = expr : (evalScan env (step env expr))
                  | otherwise      = [expr]

evalScanS :: Env -> Expr -> String
evalScanS env expr = unlines $ map show $ evalScan env expr

