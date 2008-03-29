module Expr where

import Data.List
import Data.Maybe

data Function = Function String [String] Expr
                deriving Show

data Expr = Var String
          | Num Integer
          | Plus Expr Expr
          | Monus Expr Expr
          | Mult Expr Expr
          | Div Expr Expr
          | Call String [Expr]
          | If Expr Expr Expr

instance Show Expr where
         show = foldExpr show [infop "+",infop "-",infop "*",infop "/"] id call fi
                where infop o a b = "(" ++ a ++ " " ++ o ++ " " ++ b ++ ")"
                      call f args = f ++ "(" ++ (ccat a) ++ ")"
                      ccat        = foldl1 (\a b -> a ++ "," ++ b)
                      fi p t e    = "if " ++ p ++ " then " ++ t ++ " else " ++ e ++ " fi"

funArgs :: Function -> [String]
funArgs (Function _ a _) = a

funBody :: Function -> Expr
funBody (Function _ _ b) = b

reducible :: Expr -> Bool
reducible (Num _) = False
reducible _       = True

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
                  fv v      = error "Free var"
                  fi p t e  = if p > 0 then t else e
                  fc f a    = eval env (subst (funArgs fun) a (funBody fun))
                              where (Just fun) = find (\(Function name _ _) -> name == f) env
                 

step :: [Function] -> Expr -> Expr
step _   (Num n)     = Num n
step env (Monus m n) | reducible m = (Monus (step env m) n)
                     | reducible n = (Monus m (step env n))
                     | otherwise   = Num (eval env (Monus m n))

subst :: [String] -> [Integer] -> Expr -> Expr
subst parnames vals e | length vals /= length parnames = error "Arity mismatch"
                      | otherwise                      = subst' (zip parnames vals) e

subst' :: [(String,Integer)] -> Expr -> Expr
subst' vals = foldExpr Num [Plus,Monus,Mult,Div] fv Call If
              where fv v = Num $ fromMaybe (error "Free variable") (lookup v vals)

{-
 -- call-by-name

subst :: [String] -> [Expr] -> Expr -> Expr
subst parnames vals e | length vals /= length parnames = error "Arity mismatch"
                      | otherwise                      = subst' (zip parnames vals) e

subst' :: [(String,Expr)] -> Expr -> Expr
subst' vals expr = case expr of
                        Num n     -> Num n
                        Plus m n  -> Plus (subst' vals m) (subst' vals n)
                        Monus m n -> Monus (subst' vals m) (subst' vals n)
                        Mult m n  -> Mult (subst' vals m) (subst' vals n)
                        Div m n   -> Div (subst' vals m) (subst' vals n)
                        If p t e  -> If (subst' vals p) (subst' vals t) (subst' vals e)
                        Var v     -> fromMaybe (error "Free variable") (lookup v vals)
                        Call f ar -> Call f (map (subst' vals) ar)
 -}
