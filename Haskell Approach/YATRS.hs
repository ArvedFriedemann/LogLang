module YATRS where

import Control.Monad
import Text.Parsec hiding (spaces)
import Data.Maybe

data Term a = BOT | ATOM a | VAR a | APPL (Term a) (Term a) deriving (Eq, Show)

--rule term, fact, equivalence
getFit::(Eq a) => Term a -> Term a -> Maybe [(a, Term a)]
getFit BOT BOT = Just []
getFit (ATOM x) (ATOM y)
  | x==y = Just []
  | otherwise = Nothing
getFit (VAR x) t = Just [(x, t)]
getFit (APPL m n) (APPL m' n') = do {
  x <- getFit m m';
  y <- getFit n n';
  return $ x++y
}

isPrefix::(Eq a) => Term a -> Term a -> Bool
isPrefix t1 t2 = isJust $ getFit t1 t2

fitsEq::(Eq a) => Term a -> Term a -> Bool
fitsEq t1 t2 = (isPrefix t1 t2) || (isPrefix t2 t1)

--get set of all unrelieveable equalities
eqIncons::(Eq a) => [(a, Term a)] -> [(a, [Term a])]
eqIncons matching = [(x, ls) | (x,t)<-matching, let ls = [t' | (y,t')<-matching, (x /= y || (fitsEq t t'))] ]

applyMatch::(Eq a) => [(a, Term a)] -> Term a -> Term a
applyMatch _ BOT = BOT
applyMatch _ x@(ATOM _)  = x
applyMatch match (VAR x) = fromJust $ lookup x match
applyMatch match (APPL m n) = APPL (applyMatch match m) (applyMatch match n)

--TODO unit propagation
