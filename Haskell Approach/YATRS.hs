module YATRS where

import Control.Monad
import Text.Parsec hiding (spaces)
import Data.Maybe
import Data.Maybe.HT
import Data.List

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

getCleanFit::(Eq a) => Term a -> Term a -> Maybe [(a, Term a)]
getCleanFit t1 t2 = do {
  fit <- getFit t1 t2;
  cleanMergeFit $ mergeFit fit
}

--mergeEqClasses::(Eq a) => [(a, Term a)] -> [([a], Term a)]
--mergeEqClasses [] = []
--mergeEqClasses ((x,VAR y):xs) = mergeEqClasses $ map (\(z,t) -> if z == y then (x,t) else (z,t)) xs
--mergeEqClasses (x:xs) = x:(mergeEqClasses xs)

isPrefix::(Eq a) => Term a -> Term a -> Bool
isPrefix t1 t2 = isJust $ getFit t1 t2

prefOrder::(Eq a) => Term a -> Term a -> Ordering
prefOrder t1 t2
  | t1==t2 = EQ         --TODO incorrect when it comes to variable renaming.
  | isPrefix t1 t2 = GT
  | otherwise = LT

fitsEq::(Eq a) => Term a -> Term a -> Bool
fitsEq t1 t2 = (isPrefix t1 t2) || (isPrefix t2 t1)

--get set of all unrelieveable equalities
--eqIncons::(Eq a) => [(a, Term a)] -> [(a, [Term a])]
--eqIncons matching = [(x, ls) | (x,t)<-matching, let ls = [t' | (y,t')<-matching, (x /= y || (fitsEq t t'))] ]

mergeFit::(Eq a) => [(a, Term a)] -> [(a, [Term a])]
mergeFit matching = [(x, [y | (x',y) <- matching, x==x']) | (x,_) <- matching]

cleanMergeFit::(Eq a) => [(a, [Term a])] -> Maybe [(a, Term a)]
cleanMergeFit merge = toMaybe (and [isJust y | (_,y) <- tops]) [(x,fromJust y) | (x,y) <- tops]
  where tops = [(x,highestAbstractor y) | (x,y) <- merge]

highestAbstractor::(Eq a) => [Term a] -> Maybe (Term a)
highestAbstractor [] = Nothing
highestAbstractor tms = toMaybe (and [ fitsEq t1 t2 | t1 <- tms, t2 <- tms]) $ head $ sortBy prefOrder tms

applyMatch::(Eq a) => Term a -> [(a, Term a)] -> Term a
applyMatch BOT _ = BOT
applyMatch x@(ATOM _) _ = x
applyMatch (VAR x) match = fromJust $ lookup x match
applyMatch (APPL m n) match = APPL (applyMatch m match) (applyMatch n match)

-- unit, premise, posterior, new fact
propUnit::(Eq a) => Term a -> Term a -> Term a -> Maybe (Term a)
propUnit unit prem post = (applyMatch post) <$> (getCleanFit prem unit)

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
