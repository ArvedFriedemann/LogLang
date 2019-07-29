module YATRS where

import Control.Monad
import Text.Parsec hiding (spaces, State)
import Data.Maybe
import Data.Maybe.HT
import Data.List
import Control.Monad.State
import Data.Semigroup.Foldable

data Term a = BOT | ATOM a | VAR a | APPL (Term a) (Term a) deriving (Eq, Show)
type KB a = [Term a]
type VarState a b = State ([[a]],[a]) b

scopeOn::VarState a ()
scopeOn = do {
  (scopes, vars) <- get;
  put ([]:scopes, vars)
}

scopeOff::VarState a ()
scopeOff = do {
  (x:scopes, vars) <- get;
  put (scopes, x++vars)
}

scoped::VarState a b -> VarState a b
scoped m = do{
  scopeOn;
  r <- m;
  scopeOff;
  return r
}

getVar::VarState a a
getVar = do {
  (s:scopes, x:xs) <- get;
  put ((x:s):scopes,xs);
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

getGCT::(Eq a) => Term a -> Term a -> Maybe (Term a, [(a, Term a)])
getGCT t1 t2 = do{t <- mt; return (t, eqs)}
  where (mt, eqs) = runState (getGCT' t1 t2) []

getGCT'::(Eq a) => Term a -> Term a -> State [(a,Term a)] (Maybe (Term a))
getGCT' BOT BOT = return $ Just BOT
getGCT' (ATOM x) (ATOM x')
  | x==x'= return $ Just $ ATOM x
  | otherwise = return Nothing
getGCT' (VAR x) t = do {
  eqs <- get;
  case lookup x eqs of
    Just t' -> getGCT' t t'
    Nothing -> do {
        put ((x,t):eqs);
        return $ Just t
    }
}
getGCT' t (VAR x) = getGCT' (VAR x) t
getGCT' (APPL m n) (APPL m' n') = do {
  mt1 <- getGCT' m m';
  mt2 <- getGCT' n n';
  return $ do {
    t1 <- mt1;
    t2 <- mt2;
    return $ APPL t1 t2
  }
}
getGCT' _ _ = return Nothing

{-
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
-}
