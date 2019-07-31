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
      eqs <- get;
      return $ propEq eqs <$> mt
}

propEq::(Eq a) => [(a,Term a)] -> Term a -> Term a
propEq _ BOT        = BOT
propEq _ a@(ATOM _) = a
propEq e (VAR x)    = case lookup x e of
                          Just t -> propEq e t --WARNING: may not terminate
                          Nothing -> (VAR x)
propEq e (APPL m n) = APPL (propEq e m) (propEq e n)

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



-- @pre: terms need to be decontextualised
-- unit, premise, posterior, new fact and new rule
propRule::(Eq a) => Term a -> Term a -> Term a -> [Term a]
propRule unit prem post = fromMaybe [] $ do {
  (mt,eqs) <- return $ getGCTVars unit prem;
  t <- mt;
  return $ [t, propEq eqs post]
}

-- @pre: terms need to be decontextualised
propUnit::(Eq a) => Term a -> Term a -> [Term a]
propUnit unit fact = maybeToList (getGCT unit fact)

--operator, unit, rule, outcome
propTerms::(Eq a) => Term a -> Term a -> Term a -> VarState a [Term a]
propTerms op unit t = do {
  (u, t') <- decontTerms unit t;
  return (case splitRule op t of
             Just (prem, post) -> propRule unit prem post
             Nothing -> propUnit unit t)
}



--TODO: think about it...if the rule operator get changed, isn't that just like using another universal turing machine?
--would that lead to the complexity thing you need?

splitRule::(Eq a) => Term a -> Term a -> Maybe (Term a, Term a)
splitRule op t@(APPL (APPL op' prem) post)
  | op == op' = Just (prem,post)
  | otherwise = Nothing
splitRule op t = Nothing

propKB::(Eq a) => Term a -> KB a -> VarState a (KB a)
propKB op kb = do{
  prop <- concat <$> (sequence $ [propTerms op unit rule | unit <- kb, rule <- kb]);
  return $ nub $ kb ++ prop
}

--outputTerms $ runDefVars $ propKB impOp (kbs "add zero X X. add (succ X) Y (succ Z) -> add X Y Z.")
