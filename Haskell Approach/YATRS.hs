module YATRS where

import Control.Monad
import Text.Parsec hiding (spaces, State)
import Data.Maybe
import Data.Maybe.HT
import Data.List
import Control.Monad.State

data Term a = BOT | ATOM a | VAR a | APPL (Term a) (Term a) deriving (Eq, Show)
type KB a = [Term a]
type VarState a b = State [a] b

getVar::VarState a a
getVar = do {
  (x:xs) <- get;
  put xs;
  return x
}

getVarMap::[b]-> VarState a [(b,a)]
getVarMap lst = (zip lst) <$> (sequence $ (const getVar) <$> lst)

vars::Term a -> [a]
vars BOT      = []
vars (ATOM _) = []
vars (VAR  x) = [x]
vars (APPL m n) = (vars m)++(vars n)

exchangeVars'::(Eq a) => [(a,a)] -> Term a -> Term a
exchangeVars' m t = exchangeVars ((\(x,y) -> (x, VAR y)) <$> m) t

exchangeVars::(Eq a) => [(a,Term a)] -> Term a -> Term a
exchangeVars _ BOT = BOT
exchangeVars _ a@(ATOM _) = a
exchangeVars m v@(VAR x) = fromMaybe v $ lookup x m
exchangeVars m (APPL x y) = APPL (exchangeVars m x) (exchangeVars m y)

--greatest common term. Gives out both variable replacements.
--if a match is possible, it returns the one sided variable replacements, as well as
--general variable equivalences
getGCTFit::(Eq a) => Term a -> Term a -> Maybe ([(a, Term a)],[(a, Term a)], [(a,a)])
getGCTFit BOT BOT = Just ([],[],[])
getGCTFit (ATOM x) (ATOM y)
  | x==y = Just ([],[],[])
  | otherwise = Nothing
getGCTFit (VAR x)  (VAR y)   = Just ([],[],[(x,y)])
getGCTFit (VAR x)  t         = Just ([(x,t)],[],[])
getGCTFit t        (VAR x)   = Just ([],[(x,t)],[])
getGCTFit (APPL m n) (APPL m' n') = do {
  (left , right , eq ) <- getGCTFit m m';
  (left', right', eq') <- getGCTFit n n';
  return (left++left', right++right', eq++eq')
}
getGCTFit _ _ = Nothing

minNewVarTerms::(Eq a) => Term a -> Term a -> VarState a (Term a, Term a)
minNewVarTerms t1 t2 = do {
  visec <- return $ (vars t1) `intersect` (vars t2);
  m1 <- getVarMap visec;
  m2 <- getVarMap visec;
  return $ (exchangeVars' m1 t1, exchangeVars' m2 t2)
}

getGCT::(Eq a) => Term a -> Term a -> VarState a (Maybe (Term a))
getGCT term1 term2 = do {
  (t1,t2) <- minNewVarTerms term1 term2;
  minMatch <- getGCT' t1 t2;
  return $ do { (t, fit) <- minMatch;
    fit' <- cleanMergeFit $ mergeFit fit;
    return $ exchangeVars fit' t;
  }
}

getGCT'::(Eq a) => Term a -> Term a -> VarState a (Maybe (Term a, [(a,Term a)]))
getGCT' BOT BOT = return $ Just (BOT, [])
getGCT' (ATOM x) (ATOM y)
  | x==y = return $ Just $ (ATOM x, [])
  | otherwise = return Nothing
getGCT' v@(VAR x)  t         = return $ Just (v, [(x,t)])
getGCT' t          v@(VAR x) = return $ Just (v, [(x,t)])
getGCT' (APPL m n) (APPL m' n') = do{ mt1 <- getGCT' m m'; mt2 <- getGCT' n n';
  return $ do {
    (t1, eqs1) <- mt1;
    (t2, eqs2) <- mt2;
    return $ (APPL t1 t2, eqs1 ++ eqs2)
  }
}

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
propTerms op unit t = (uncurry $ propUnit unit) $ splitRule op t
--TODO: think about it...if the rule operator get changed, isn't that just like using another universal turing machine?
--would that lead to the complexity thing you need?

splitRule::(Eq a) => Term a -> Term a -> (Term a, Term a)
splitRule op t@(APPL (APPL op' prem) post)
  | op == op' = (prem,post)
  | otherwise = (t,t)
splitRule op t = (t,t)

propKB::(Eq a) => Term a -> KB a -> KB a
propKB op kb = nub $ kb ++ (catMaybes [propTerms op unit rule | unit <- kb, rule <- kb])

consequences::(Eq a) => Term a -> Term a -> KB a -> [Term a]
consequences op t kb = catMaybes (propTerms op t <$> kb)
