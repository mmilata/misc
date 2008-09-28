module Expr
   ( Expr(Var, Num, Plus, Monus, Mult, Div, Call, If),
     Function(Function), Env, funName, funArgs, funBody, calls,
     freeVars, parmlist, evalScan, evalScanS, debugShowExpr ) where
-- $Id$

import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Reader

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

getFunction :: String -> Reader Env Function
getFunction str = do e <- ask
                     case find (\(Function name _ _) -> name == str) e of
                       Nothing -> error "Function not in environment"
                       Just f  -> return f

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

eval :: Expr -> Reader Env Integer
eval = do let monus a b = if a-b < 0 then 0 else a-b
              mydiv a b = if b == 0 then 0 else a `div` b
              fi p t e  = if p > 0 then t else e
              fv v      = error "Free variable"
              fc f a    = do a' <- sequence a
                             fun <- getFunction f
                             eval (subst (funArgs fun) a' (funBody fun))
          foldExpr return [liftM2 (+),liftM2 monus,liftM2 (*),liftM2 mydiv] fv fc (liftM3 fi)

step :: Expr -> Reader Env Expr
step (Num n)     = return $ Num n
step (Var v)     = error "Free variable"
step (If p t e)  | reducible p = do { p' <- step p; return (If p' t e) }
                 | otherwise   = do { n <- eval p; return $ if n > 0 then t else e }
step (Call f ar) | all (not.reducible) ar = do args <- mapM eval ar
                                               fun <- getFunction f
                                               return $ subst (funArgs fun) args (funBody fun)
                 | otherwise              = do { ar' <- liststep ar; return (Call f ar') }
step (Monus m n) = binstep Monus m n
step (Plus m n)  = binstep Plus m n
step (Mult m n)  = binstep Mult m n
step (Div m n)   = binstep Div m n

binstep :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Reader Env Expr
binstep con m n | reducible m = do { m' <- step m; return (con m' n) }
                | reducible n = do { n' <- step n; return (con m n') }
                | otherwise   = do { n <- eval (con m n); return (Num n) }

liststep :: [Expr] -> Reader Env [Expr]
liststep (x:xs) | reducible x = do x' <- step x
                                   return (x':xs)
                | otherwise   = do xs' <- liststep xs
                                   return (x:xs')

subst :: [String] -> [Integer] -> Expr -> Expr
subst parnames vals e | length vals /= length parnames = error "Arity mismatch"
                      | otherwise                      = subst' (zip parnames vals) e

subst' :: [(String,Integer)] -> Expr -> Expr
subst' vals = foldExpr Num [Plus,Monus,Mult,Div] fv Call If
              where fv v = Num $ fromMaybe (error "Free variable") (lookup v vals)

parmlist :: [String] -> String
parmlist [w]    = w
parmlist (w:ws) = w ++ ',':(parmlist ws)

evalScan :: Expr -> Reader Env [Expr]
evalScan expr | reducible expr = do expr' <- step expr
                                    rest <- evalScan expr'
                                    return (expr : rest)
              | otherwise      = return [expr]

evalScanS :: Expr -> Reader Env String
evalScanS expr = do x <- evalScan expr
                    return $ unlines $ map show x
