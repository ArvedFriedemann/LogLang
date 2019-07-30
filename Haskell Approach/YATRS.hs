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

{-
termToString <$> getGCT (ts "add X (succ X)") (ts "add zero Y")
TODO: use nice variable names after term matching!
-}

decontTerms::(Eq a) => Term a -> Term a -> VarState a (Term a, Term a)
decontTerms t1 t2 = do {
  confVars <- return $ vars t1 `intersect` vars t2;
  m1 <- getVarMap confVars;
  m2 <- getVarMap confVars;
  return (exchangeVars' m1 t1, exchangeVars' m2 t2)
}

getGCTdecon::(Eq a) => Term a -> Term a -> VarState a (Maybe (Term a))
getGCTdecon t1 t2 = do {
  (dt1, dt2) <- decontTerms t1 t2;
  return $ getGCT dt1 dt2
}

getGCTVars::(Eq a) => Term a -> Term a -> (Maybe (Term a), [(a, Term a)])
getGCTVars t1 t2 = runState (getGCT' t1 t2) []

getGCT::(Eq a) => Term a -> Term a -> Maybe (Term a)
getGCT t1 t2 = evalState (getGCT' t1 t2) []

getGCT'::(Eq a) => Term a -> Term a -> State [(a,Term a)] (Maybe (Term a))
getGCT' t1 t2 = do {
      mt <- getMCT t1 t2;
      case propEq <$> mt of
          Just act -> act >>= (\res ->return $ Just res)
          Nothing -> return Nothing
}

propEq::(Eq a) => Term a -> State [(a,Term a)] (Term a)
propEq BOT        = return BOT
propEq a@(ATOM _) = return a
propEq (VAR x)    = do{
  eqs <- get;
  case lookup x eqs of
    Just t -> propEq t --WARNING: may not terminate
    Nothing -> return (VAR x)
}
propEq (APPL m n) = do{
  t1 <- propEq m;
  t2 <- propEq n;
  return $ APPL t1 t2
}

getMCT::(Eq a) => Term a -> Term a -> State [(a,Term a)] (Maybe (Term a))
getMCT BOT BOT = return $ Just BOT
getMCT (ATOM x) (ATOM x')
  | x==x' = return $ Just (ATOM x)
  | otherwise = return Nothing
getMCT (VAR x) t = do{
  eqs <- get;
  ma <- (case lookup x eqs of
            Just t' -> do {
                            mtu <- getGCT' t t';
                            return $ (\tu -> put $ (x,tu):(delete (x,t') eqs)) <$> mtu;
                          }
            Nothing -> return $ Just $ put $ (x,t):eqs);
  (case ma of
    Just act -> act >> (return $ Just (VAR x))
    Nothing  -> return Nothing)
}
getMCT t (VAR x) = getMCT (VAR x) t
getMCT (APPL m n) (APPL m' n') = do{
  mt1 <- getMCT m m';
  mt2 <- getMCT n n';
  return $ do {
    t1 <- mt1;
    t2 <- mt2;
    return $ APPL t1 t2
  }
}
getMCT _ _ = return Nothing


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
