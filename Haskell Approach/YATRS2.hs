module YATRS2 where

import Control.Monad
import Text.Parsec hiding (spaces)
import Data.Maybe
import Control.Monad.State

data IdTerm a = IBOT | IVAR a | IATOM a | IAPPL a a deriving (Show, Eq)
type IdxTerm a = (a,IdTerm a)

--VARC: variable name to term
--VEQ: equality by exact value (also same varnames)
data Constraint a = CBOT | EQ a a | VEQ a a | UNIF a a | VARC a (IdTerm a) | PRET a (IdTerm a) deriving (Show, Eq)

type VarState a = State ([a], CTX a)
type CTX a = [IdxTerm a]

getVar::VarState a a
getVar = do {
  ((v:vars), ctx) <- get;
  put (vars, ctx);
  return v
}


propConstraint::(Eq a) => Constraint (a, Maybe a) -> VarState a [Constraint a]
propConstraint CBOT = return [CBOT]
propConstraint (EQ (k,_) (k',_))
  | k==k' = return []
  | otherwise = return [CBOT]
-----------VEQ-----------------------------------------------------
propConstraint (VEQ (k, Just (IBOT)) (k', Just (IBOT))) = return []
propConstraint (VEQ (k, Just (IVAR x)) (k', Just (IVAR y)))
  | x==y = return []
  | otherwise = return [CBOT]
propConstraint (VEQ (k, Just (IATOM x)) (k', Just (IATOM y)))
  | x==y = return []
  | otherwise = return [CBOT]
propConstraint (VEQ (k, Just (IAPPL x y)) (k', Just (IAPPL x y))) = return [VEQ x x', VEQ y y']

propConstraint (VEQ (k, Nothing) (k', Just t)) = ((VEQ k k'):) <$> updateCTXconstr k' t

propConstraint (VEQ (k,Just t) (k', Nothing)) = propConstraint (VEQ (k', Nothing) (k,Just t))
propConstraint c@(VEQ (k', Nothing) (k, Nothing)) = return [c]
propConstraint (VEQ _ _) = return [CBOT]
----------UNIF----------------------------------------------------
propConstraint (UNIF (k, Just (IVAR x)) (k', Just t)) = return [VARC x t, UNIF k k']
propConstraint (UNIF (k', Just t) (k, Just (IVAR x))) = return [VARC x t, UNIF k' k]
propConstraint (UNIF (k, Just (IAPPL x y)), (k', Just (IAPPL x' y'))) = return [UNIF x x', UNIF y y']

propConstraint (UNIF (k, Just t) (k', Nothing)) = ((UNIF k k'):) <$> updateCTXconstr k' t
propConstraint (UNIF (k, Nothing) (k', Just t)) = propConstraint (k', Just t) (k, Nothing)

propConstraint (UNIF a b) = propConstraint $ VEQ a b --TODO: check







propConstraint::(Eq a) => Constraint a -> VarState a [Constraint a]
propConstraint CBOT = return [CBOT]
propConstraint (EQ a b)
  | a==b = return []
  | otherwise = return [CBOT]
propConstraint (UNIF a b) =
  | a==b = return []
  |otherwise = do {
    (_, ctx) <- get;
    case (lookup a ctx, lookup b ctx) of
        (Just t, Just t') -> return $ caseUnif t t'
        (Nothing, Just t)     -> return $ [EQT a t, UNIF a b] --TODO: dangling reference?
        (Just t, Nothing)     -> return $ [EQT b t, UNIF a b] --TODO: dangling reference?
        (Nothing, Nothing)        -> return $ [UNIF a b]
  }
propConstraint (EQT a t) = do {
  (_, ctx) <- get;

}

updateCTX::a -> IdTerm a -> VarState a [Constraint a]
updateCTX addr term = TODO. Remember to instantiate variables if needed

updateCTXconstr::a -> IdTerm a -> VarState a [Constraint a]
updateCTXconstr a IBOT = do {
  (v,ctx) <- get;
  case lookup a cxt of
    Just IBOT -> return []
    Just _    -> return [CBOT]
    Nothing   -> (put (v, (a, IBOT):ctx)) >> return []
}
updateCTXconstr a (IATOM _) = do {
  (v:vars,ctx) <- get;
  case lookup a ctx of
    Just (IATOM _) -> return []
    Just _         -> return [CBOT]
    Nothing        -> (put (vars, (a, IATOM v):ctx) ) >> return []
}
updateCTXconstr a (IVAR _) = do {
  (v:vars,ctx) <- get;
  case lookup a ctx of
    Just (IVAR _) ->  return []
    Just _         -> return [CBOT]
    Nothing        -> (put (vars, (a, IATOM v):ctx) ) >> return []
}

updateCTXconstr a (IAPPL _ _) = do {
  (v:v':vars,ctx) <- get;
  case lookup a ctx of
    Just (IAPPL _ _) ->  return []
    Just _         -> return [CBOT]
    Nothing        -> (put (vars, (a, IAPPL v v'):ctx) ) >> return []
}


--TODO: clause learning through adding new constraints when values are being filled (e.g. other constraints are satisfied)


caseUnif::IdxTerm a -> IdxTerm a -> [Constraint a]
caseUnif (_,IBOT) (_,IBOT) = []
caseUnif (_,IATOM x) (_,IATOM y) = [EQ x y]
caseUnif (k,IVAR _) (k',IVAR _) = [UNIF k k']
caseUnif (k,IVAR x) (k', t)     = [VARC x t, UNIF k k'] --TODO: ALL VARS!
caseUnif (k', t) (k,IVAR x)     = [VARC x t, UNIF k k'] --TODO: ALL VARS!
caseUnif (_,IAPPL a b) (_, IAPPL a' b') = [UNIF a a', UNIF b b']
caseUNIF _ _ = [CBOT]



lookupWithKey::(Eq a) => (a -> Bool) -> [(a,b)] -> Maybe (a,b)
lookupWithKey _ [] = Nothing
lookupWithKey fkt ((x,y):xs)
  | fkt x = Just (x,y)
  | otherwise = lookupWithKey fkt xs
