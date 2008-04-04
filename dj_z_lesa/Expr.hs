module Expr where

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
           deriving Show

data Function = Function String [String] Expr
                deriving Show

toStr :: Expr -> String
toStr = foldExpr show [infop "+",infop "-",infop "*",infop "/"] id call fi
                where infop o a b = "(" ++ a ++ " " ++ o ++ " " ++ b ++ ")"
                      call f args = f ++ "(" ++ (parmlist args) ++ ")"
                      fi p t e    = "if " ++ p ++ " then " ++ t ++ " else " ++ e ++ " fi"

fToStr (Function name args body) = name ++ "(" ++ parmlist args ++ ") = " ++ toStr body

funArgs :: Function -> [String]
funArgs (Function _ a _) = a

funBody :: Function -> Expr
funBody (Function _ _ b) = b

reducible :: Expr -> Bool
reducible (Num _) = False
reducible _       = True

-- zjisti jestli funkce neobsahuje volne promenne
checkFunction :: Function -> Bool
checkFunction (Function _ parms body) = foldExpr (const True) (repeat (&&)) fv fc fi body
                                        where fc _ args = and args
                                              fi p t e  = p && t && e
                                              fv v      = v `elem` parms

foldExpr :: (Integer -> a)       -- funkce na cislech
         -> [a -> a -> a]        -- funkce na binarnich operacich [+,-,*,/]
         -> (String -> a)        -- funkce na promennych
         -> (String -> [a] -> a) -- funkce na volanich
         -> (a -> a -> a -> a)   -- funkce na ifu
         -> Expr                 -- vyraz
         -> a
foldExpr f _ _ _ _ (Num n)     = f n
foldExpr l b v c i (Plus m n)  = (b!!0) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr l b v c i (Monus m n) = (b!!1) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr l b v c i (Mult m n)  = (b!!2) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr l b v c i (Div m n)   = (b!!3) (foldExpr l b v c i m) (foldExpr l b v c i n)
foldExpr _ _ v _ _ (Var x)     = v x
foldExpr l b v c i (Call f ar) = c f (map (foldExpr l b v c i) ar)
foldExpr l b v c i (If p t e)  = i (foldExpr l b v c i p) (foldExpr l b v c i t) (foldExpr l b v c i e)

eval :: [Function] -> Expr -> Integer
eval env = foldExpr id [(+),monus,(*),mydiv] fv fc fi
            where monus a b = if a-b < 0 then 0 else a-b
                  mydiv a b = if b == 0 then 0 else a `div` b
                  fv v      = error "Free variable"
                  fi p t e  = if p > 0 then t else e
                  fc f a    = eval env (subst (funArgs fun) a (funBody fun))
                              where (Just fun) = find (\(Function name _ _) -> name == f) env

step :: [Function] -> Expr -> Expr
step _   (Num n)     = Num n
step env (Var v)     = error "Free variable"
step env (If p t e)  | reducible p = (If (step env p) t e)
                     | otherwise   = if (eval env p) > 0 then t else e
step env (Call f ar) | all (not.reducible) ar = subst (funArgs fun) (map (eval env) ar) (funBody fun)
                     | otherwise              = (Call f (liststep ar))
                       where (Just fun)      = find (\(Function name _ _) -> name == f) env
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

scan :: [Function] -> Expr -> String
scan env expr | reducible expr = toStr expr ++ "\n" ++ scan env (step env expr)
              | otherwise      = toStr expr ++ "\n"

