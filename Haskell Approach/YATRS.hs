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
getFit (VAR x) t = Just [(x, t)] --warning: t can be a variable as well!
getFit (APPL m n) (APPL m' n') = do {
  x <- getFit m m';
  y <- getFit n n';
  return $ x++y
}
getFit _ _ = Nothing

--TODO: this matching should just give more constraints. Maybe equality and conjunction os something
--should be atomic constraints.

propagateEq::(Eq a) => [(a, Term a)] -> Maybe [(a, Term a)]
propagateEq eqs = []

isPrefix::(Eq a) => Term a -> Term a -> Bool
isPrefix t1 t2 = isJust $ getFit t1 t2

fitsEq::(Eq a) => Term a -> Term a -> Bool
fitsEq t1 t2 = (isPrefix t1 t2) || (isPrefix t2 t1)

--get set of all unrelieveable equalities
eqIncons::(Eq a) => [(a, Term a)] -> [(a, [Term a])]
eqIncons matching = [(x, ls) | (x,t)<-matching, let ls = [t' | (y,t')<-matching, (x /= y || (fitsEq t t'))] ]

--satEq::(Eq a) => [(a, [Term a])] -> Bool
--satEq eqs =

applyMatch::(Eq a) => Term a -> [(a, Term a)] -> Term a
applyMatch BOT _ = BOT
applyMatch x@(ATOM _) _ = x
applyMatch (VAR x) match = fromJust $ lookup x match
applyMatch (APPL m n) match = APPL (applyMatch m match) (applyMatch n match)

-- unit, premise, posterior, new fact
propUnit::(Eq a) => Term a -> Term a -> Term a -> Maybe (Term a)
propUnit unit prem post = (applyMatch post) <$> (getFit prem unit)

--operator, unit, rule, outcome
propTerms::(Eq a) => Term a -> Term a -> Term a -> Maybe (Term a)
propTerms op unit (APPL (APPL op' prem) post)
  | op == op' = propUnit unit prem post
  | otherwise = Nothing
propTerms _ _ _ = Nothing
--TODO: think about it...if the rule operator get changed, isn't that just like using another universal turing machine?
--would that lead to the complexity thing you need?

propKB::(Eq a) => Term a -> [Term a] -> [Term a]
propKB op kb = kb ++ (catMaybes [propTerms op unit rule | unit <- kb, rule <- kb])
