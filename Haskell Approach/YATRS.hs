module YATRS where

import Control.Monad
import Text.Parsec hiding (spaces, State)
import Data.Maybe
--import Data.Maybe.HT
import Data.List hiding (lookupWithKey)
import Control.Monad.State hiding (foldM)
--import Data.Semigroup.Foldable

data Term a = BOT | ATOM a | VAR a | APPL (Term a) (Term a) deriving (Eq, Show)
type KB a = [Term a]
type VarState a b = State ([[a]],[a]) b
type TermEq a = [([a],Term a)]

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
  m2 <- getVarMap confVars;
  return (t1, exchangeVars' m2 t2)
}

alphaEq::(Eq a) => Term a -> Term a -> Bool
alphaEq t1 t2 = evalState (alphaEq' t1 t2) []

alphaEq'::(Eq a) => Term a -> Term a -> State [(a,a)] Bool
alphaEq' BOT BOT = return True
alphaEq' (ATOM x) (ATOM y) = return $ x==y
alphaEq' (VAR x) (VAR y) = do {
  eqs <- get;
  contx <- return $ [(a,b) | (a,b) <- eqs, a == x || b == x];
  conty <- return $ [(a,b) | (a,b) <- eqs, a == y || b == y];
  if (null contx) && (null conty) then (put $ (x,y):eqs) >> return True else
    return $ and [ (a==x && b==y) || (a==y && b==x) | (a,b) <- contx ++ conty]
}
alphaEq' (APPL m n) (APPL m' n') = do {
  t1 <- alphaEq' m m';
  t2 <- alphaEq' n n';
  return $ t1 && t2;
}
alphaEq' _ _ = return False

getGCTdecon::(Eq a) => Term a -> Term a -> VarState a (Maybe (Term a))
getGCTdecon t1 t2 = do {
  (dt1, dt2) <- decontTerms t1 t2;
  return $ getGCT dt1 dt2
}

getGCTVars::(Eq a) => Term a -> Term a -> (Maybe (Term a), TermEq a)
getGCTVars t1 t2 = runState (getGCT' t1 t2) []

getGCT::(Eq a) => Term a -> Term a -> Maybe (Term a)
getGCT t1 t2 = evalState (getGCT' t1 t2) []

getGCT'::(Eq a) => Term a -> Term a -> State (TermEq a) (Maybe (Term a))
getGCT' t1 t2 = do {
      mt <- getMCT t1 t2;
      eqs <- get;
      return $ propEq eqs <$> mt
}

propEq::(Eq a) => TermEq a -> Term a -> Term a
propEq _ BOT        = BOT
propEq _ a@(ATOM _) = a
propEq e (VAR x)    = case lookupWithKey (elem x) e of
                          Just (xs,t) -> case t of
                                          (VAR x') -> if elem x' xs then (VAR $ head xs) else propEq e t
                                          _ -> propEq e t
                          Nothing -> (VAR x)
propEq e (APPL m n) = APPL (propEq e m) (propEq e n)

getMCT::(Eq a) => Term a -> Term a -> State (TermEq a) (Maybe (Term a))
getMCT BOT BOT = return $ Just BOT
getMCT (ATOM x) (ATOM x')
  | x==x' = return $ Just (ATOM x)
  | otherwise = return Nothing
getMCT (VAR x) (VAR y) = do {
  eqs <- get;
  mact <- return $ do {
    (a,t) <- lookupWithKey (elem x) eqs;
    (b,t')<- lookupWithKey (elem y) eqs;
    if (a /= b) then
          return (do {
            mt'' <- getGCT' t t';
            case mt'' of
              Just t'' -> do {
                  eqs' <- get;
                  put $ (union a b, t''):(delete (b,t') $ delete (a,t) eqs);
                  return $ Just (VAR x)
                }
              Nothing -> return Nothing
          })
    else
          return $ return $ Just t
  };
  (case mact of
    Just act -> act
    Nothing -> do {
      case lookupWithKey (\k->(elem x k) || (elem y k)) eqs of
        Just (a,t) -> (put $ (union a [x,y], t):(delete (a,t) eqs)) >> return (Just t)
        Nothing -> modify ((:) ([x,y], VAR x)) >> return (Just $ VAR x)
    })
}
getMCT (VAR x) t = do {
  eqs <- get;
  ma <- (case lookupWithKey (elem x) eqs of
            Just (x',t') -> do {
                            mtu <- getGCT' t t';
                            return $ (\tu -> put $ (x',tu):(delete (x',t') eqs)) <$> mtu;
                          }
            Nothing -> return $ Just $ put $ ([x],t):eqs);
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


-- propRule::(Eq a) =>Term a -> Term a -> Term a -> Term a -> [Term a]
-- propRule op unit prem post = fromMaybe [] $ do {
--   (t, eqs) <- tupMab1 $ getGCTVars unit prem;
--   return $ [APPL (APPL op t) (propEq eqs post)]
-- }
propRule::(Eq a) =>Term a -> Term a -> Term a -> Term a -> State (TermEq a) [Term a]
propRule op unit prem post = do {
  preTerms  <- propUnit unit prem;
  postTerms <- return $ Nothing;--propUnit unit post;
  eqs <- get;
  case (preTerms, postTerms) of
    (Just t, Nothing) -> return $ [propEq eqs post] --[APPL (APPL op t) (propEq eqs post)]
    (Nothing, Just t) -> return $ [propEq eqs prem,t]
    (Just t, Just t') -> return $ [t,t']
    (Nothing, Nothing)-> return $ []
}

--propUnit::(Eq a) => Term a -> Term a -> Maybe (Term a, TermEq a)
--propUnit unit fact = tupMab1 $ getGCTVars unit fact
propUnit::(Eq a) => Term a -> Term a -> State (TermEq a) (Maybe (Term a))
propUnit unit fact = do {
  eqs <- get;
  res <- getGCT' unit fact;
  if isJust res then return () else put eqs;
  return res
}

propTerm::(Eq a) => Term a -> Term a -> Term a -> VarState a [Term a]
propTerm op unit term = do {
  (u, t) <- decontTerms unit term;
  return $ evalState (propTerm' op u t) []
}

propTerm'::(Eq a) => Term a -> Term a -> Term a -> State (TermEq a) [Term a]
propTerm' op unit term = fromMaybe (maybeToList <$> propUnit unit term) $ do {
                            (prem, post) <- splitRule op term;
                            return $ propRule op unit prem post
                          }

propTerm''::(Eq a) => Term a -> Term a -> Term a -> [Term a]
propTerm'' op unit term = evalState (propTerm' op unit term) []


--TODO: think about it...if the rule operator get changed, isn't that just like using another universal turing machine?
--would that lead to the complexity thing you need?

splitRule::(Eq a) => Term a -> Term a -> Maybe (Term a, Term a)
splitRule op t@(APPL (APPL op' prem) post)
  | op == op' = Just (prem,post)
  | otherwise = Nothing
splitRule op t = Nothing

decontKB::(Eq a) => KB a -> VarState a (KB a)
decontKB kb = sequence [foldM (\x y -> snd <$> decontTerms y x) a (delete a kb) | a <- kb] --doesn't work

propKB::(Eq a) => Term a -> KB a -> VarState a (KB a)
propKB op kb = do{
  prop <- return $ concat $ ([propTerm'' op unit rule | unit <- kb, rule <- kb, unit /= rule]);
  return $ nubWith alphaEq $ kb ++ prop
}

propKBArbit::(Eq a) => Term a -> KB a -> VarState a (KB a)
propKBArbit op kb = (propKBArbit' op) =<< (decontKB kb)

propKBArbit'::(Eq a) => Term a -> KB a -> VarState a (KB a)
propKBArbit' op kb = do {
  next <- propKB op kb;
  if next == kb then return kb else propKBArbit op next;
}

--outputTerms $ runDefVars $ propKBArbit impOp (kbs "add zero X X. add (succ X) Y (succ Z) -> add X Y Z. add (succ zero) (succ (succ zero)) X.")

nubWith::(a->a->Bool) -> [a]->[a]
nubWith eq [] = []
nubWith eq (x:xs) = x:(nubWith eq $ filter (not.(eq x)) xs )

lookupWith::(Eq a) => (a -> Bool) -> [(a,b)] -> Maybe b
lookupWith _ [] = Nothing
lookupWith fkt ((x,y):xs)
  | fkt x = Just y
  | otherwise = lookupWith fkt xs

lookupWithKey::(Eq a) => (a -> Bool) -> [(a,b)] -> Maybe (a,b)
lookupWithKey _ [] = Nothing
lookupWithKey fkt ((x,y):xs)
  | fkt x = Just (x,y)
  | otherwise = lookupWithKey fkt xs

tupMab1::(Maybe a, b) -> Maybe (a,b)
tupMab1 (x',y) = x' >>= (\x -> Just (x,y))
