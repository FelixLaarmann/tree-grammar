{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}


module Term where
import Control.Unification
import Data.Functor.Fixedpoint
import Control.Unification.IntVar
import Control.Unification.Types
import Data.Maybe
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Trans
import Data.List
import Data.Either

{-
Ground Terms
-}
data Term t = Symbol !t | App !(Term t) !(Term t) deriving (Show, Eq, Ord, Traversable, Functor, Foldable)

{-
functions on ground terms
-}
arguments :: Term t -> [Term t]
arguments (Symbol _) = []
arguments (App (Symbol f) r) = [r]
arguments (App l r) = arguments' l [r] where
  arguments' (App (Symbol f) r) s = r : s
  arguments' (App l r) s = arguments' l (arguments' r s)
  arguments' x s = x : s

root :: Term t -> t
root (Symbol f) = f
root (App l r) = root l

findSymbols :: Eq t => Term t -> [(t, Int)]
findSymbols (Symbol f) = [(f, 0)]
findSymbols (App l r) = nub $ let args = arguments (App l r) in [(root l, length $ args)] ++ (args >>= findSymbols)
--make findSymbols tail-recursive?!

treeToTerm :: t -> [Term t] -> Term t
treeToTerm f args = foldl' App (Symbol f) args

{-
subTerms computes the list of all subterms of a given term
-}
subTerms :: Term t -> [Term t]
subTerms (Symbol x) = [Symbol x]
subTerms t = (t:) $ (arguments t >>= subTerms)

{-
strictSubTerms computes the list of all strict subterms of a given term
-}
strictSubTerms ::Term t -> [Term t]
strictSubTerms t = arguments t >>= subTerms

{-
pos returns the list of all positions of a Term
-}
pos :: Term t -> [Pos]
pos (Symbol _) = [[]]
pos t = pos' $ zip (arguments t) [1..] where
  pos' [] = [[]]
  pos' ((t,n) : ps) = (map (\ns -> n:ns) (pos t)) ++ pos' ps

termAtPos :: Term t -> Pos -> Maybe (Term t)
termAtPos t [] = Just $ t 
termAtPos t (n:ps) = let args = arguments t in
  if (length args < n && n > 0) then Nothing else termAtPos ((arguments t)!!(n-1)) ps

symbolAtPos :: Term t -> Pos -> Maybe t
symbolAtPos t [] = Just $ root t 
symbolAtPos t (n:ps) = let args = arguments t in
  if (length args < n && n > 0) then Nothing else symbolAtPos ((arguments t)!!(n-1)) ps

posTerm :: Term t -> Term Pos
posTerm t = treeToTerm [] $ map (positions []) $ zip (arguments t) [1..] where
  positions p (ti, i) = let pi = p ++ [i] in treeToTerm pi $ map (positions pi) $ zip (arguments ti) [1..]

--mapTerm :: (t -> t') -> Term t -> Term t'
--mapTerm = fmap

mapOverPos :: (Pos -> Maybe t') -> Term t -> Maybe (Term t')
mapOverPos f t = noNothing $ fmap f $ posTerm t where
  noNothing (Symbol (Just s)) = Just $ Symbol s
  noNothing (Symbol Nothing) = Nothing
  noNothing (App l r) = do
    l' <- noNothing l
    r' <- noNothing r
    return $ App l' r'

substituteAtPos :: Term t -> Term t -> Pos -> Maybe (Term t)
substituteAtPos t t' [] = Just t'
substituteAtPos t t' (p : ps) = do
    guard $ length args < p && p > 0
    args' <- sequence $ applyAt (p-1) (\x -> substituteAtPos x t' ps) args
    return $ treeToTerm (root t) args'
  where args = arguments t
        applyAt _ f [] = [Nothing]
        applyAt 0 f (l : ls) = (f l) : map Just ls
        applyAt n f (l : ls) = (Just l) : applyAt (n-1) f ls

depth ::Term t -> Int
depth = maximum . (map length) . pos

{-
lpo is a lexicographic path ordering on ground terms >_lpo
-}
lpo :: (Ord t) => Term t -> Term t -> Bool
lpo (Symbol f) (Symbol g) = f > g --constants are compared by the order on the signature
lpo s t = a || b || c where
  a = (or $ map (\i -> lpo i t) si) || (or $ map (== t) si)
  b = (f > g) && (and $ map (lpo s) ti)
  c = (f == g) && case findIndex (not) $ zipWith (==) si ti of
    Nothing -> False
    Just i -> (lpo (si !! i) (ti !! i)) && (and $ map (lpo s) $ drop (i+1) ti)
  f = root s
  g = root t
  si = arguments s
  ti = arguments t


{-
terms over variables that support unification-fd
-}
data TermV t v = SymbolV !t | AppV !v !v deriving (Show, Eq, Ord, Traversable, Functor, Foldable)

instance Eq t => Unifiable (TermV t) where
  zipMatch (SymbolV x) (SymbolV y) | (x == y) = Just (SymbolV x)
  zipMatch (AppV l1 r1) (AppV l2 r2) = Just (AppV (Right (l1,l2)) (Right (r1,r2)))
  zipMatch _ _ = Nothing

eqUTerm :: (Eq t, Eq v) => UTerm (TermV t) v -> UTerm (TermV t) v -> Bool
eqUTerm (UVar x) (UVar y) = x == y
eqUTerm (UTerm (SymbolV f)) (UTerm (SymbolV g)) = f == g
eqUTerm (UTerm (AppV l r)) (UTerm (AppV l' r')) = eqUTerm l l' && eqUTerm r r'
eqUTerm _ _ = False

instance (Eq t, Eq v) => Eq (UTerm (TermV t) v) where
  (==) = eqUTerm

leqUTerm :: (Ord t, Eq v) => UTerm (TermV t) v -> UTerm (TermV t) v -> Bool
leqUTerm (UVar x) (UVar y) = x == y
leqUTerm (UTerm (SymbolV f)) (UTerm (SymbolV g)) = f <= g
leqUTerm (UTerm (AppV l r)) (UTerm (AppV l' r')) = leqUTerm l l' && leqUTerm r r'
leqUTerm _ _ = False

instance (Ord t, Eq v) => Ord (UTerm (TermV t) v) where
  l <= r = leqUTerm r l

{-
Concrete BindingMonad instance for computations over terms
-}
type BspFailure =  UFailure (TermV String) IntVar
type FallibleBindingMonad = ExceptT BspFailure (IntBindingT (TermV String) Identity)

runFBM :: FallibleBindingMonad a -> (Either BspFailure a, IntBindingState (TermV String))
runFBM = runIdentity . runIntBindingT . runExceptT

evalFBM :: FallibleBindingMonad a -> Either BspFailure a
evalFBM = runIdentity . evalIntBindingT . runExceptT

execFBM :: FallibleBindingMonad a -> IntBindingState (TermV String)
execFBM = runIdentity . execIntBindingT . runExceptT

{-
linearize returns the linearization of the input term
-}
linearize :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
              UTerm (TermV t) v -> em m (UTerm (TermV t) v)
linearize (UTerm (SymbolV x)) = return . UTerm $ SymbolV x
linearize (UTerm (AppV l r)) = do
  l' <- linearize l
  r' <- linearize r
  return . UTerm $ AppV l' r'
linearize (UVar _) = fmap UVar $ lift freeVar


{-
isLinear tests if a given term is linear
-}
isLinearInCtxt :: Eq v => UTerm (TermV t) v -> [v] -> (Bool, [v])
isLinearInCtxt (UTerm (SymbolV x)) ctxt = (True, ctxt)
isLinearInCtxt (UTerm (AppV l r)) ctxt = let le = (isLinearInCtxt l ctxt)  in
  let re = (isLinearInCtxt r (snd le)) in
    ((fst le) && (fst re), snd re)
isLinearInCtxt (UVar x) ctxt = if (elem x ctxt) then (False, ctxt) else (True, x : ctxt)

isLinear :: Eq v => UTerm (TermV t) v -> Bool
isLinear = fst . (flip isLinearInCtxt [])

{-
functions on terms over variables
-}
argumentsV :: UTerm (TermV t) v -> [UTerm (TermV t) v]
argumentsV (UTerm (SymbolV _)) = []
argumentsV (UTerm (AppV (UTerm (SymbolV f)) r)) = [r]
argumentsV (UTerm (AppV l r)) = argumentsV' l [r] where
  argumentsV' (UTerm (AppV (UTerm (SymbolV f)) r)) s = r : s
  argumentsV' (UTerm (AppV l r)) s = argumentsV' l (argumentsV' r s)
  argumentsV' x s = x : s

rootV :: UTerm (TermV t) v -> Either v t
rootV (UVar v) = Left v
rootV (UTerm (SymbolV f)) = Right f
rootV (UTerm (AppV l r)) = rootV l

findSymbolsV :: Eq t => UTerm (TermV t) v -> [(t, Int)]
findSymbolsV (UVar _) = []
findSymbolsV (UTerm (SymbolV f)) = [(f, 0)]
findSymbolsV (UTerm (AppV l r)) = nub $ case rootV l of
    Right s -> let args = argumentsV (UTerm (AppV l r)) in [(s, length $ args)] ++ (args >>= findSymbolsV)
    Left _ -> []

treeToTermV :: t -> [UTerm (TermV t) v] -> UTerm (TermV t) v
treeToTermV f args = foldl (\t t' -> UTerm $ AppV t t') (UTerm (SymbolV f)) args

{-
subTerms computes the list of all subterms of a given term
-}
subTermsV :: UTerm (TermV t) v -> [UTerm (TermV t) v]
subTermsV (UVar x) = [UVar x]
subTermsV (UTerm (SymbolV x)) = [UTerm $ SymbolV x]
subTermsV t = (t:) $ (argumentsV t >>= subTermsV)

{-
strictSubTerms computes the list of all strict subterms of a given term
-}
strictSubTermsV :: UTerm (TermV t) v -> [UTerm (TermV t) v]
strictSubTermsV (UVar x) = []
strictSubTermsV t = argumentsV t >>= subTermsV


type Pos = [Int] 
{-
vars returns all variable of a term together with their position.
If a variable occurs in multiple positions, it occurs multiple times in the result.
-}
vars :: UTerm (TermV t) v -> [(v, Pos)]
vars (UVar x) = [(x, [])]
vars (UTerm (SymbolV _)) = []
vars t = vars' $ zip (argumentsV t) [1..] where
  vars' [] = []
  vars' ((t,n) : ps) = (map (\(v,ns) -> (v, n:ns)) (vars t)) ++ vars' ps

{-
pos returns the list of all positions of a Term
-}
posV :: UTerm (TermV t) v -> [Pos]
posV (UVar _) = [[]]
posV (UTerm (SymbolV _)) = [[]]
posV t = posV' $ zip (argumentsV t) [1..] where
  posV' [] = [[]]
  posV' ((t,n) : ps) = (map (\ns -> n:ns) (posV t)) ++ posV' ps

termAtPosV :: UTerm (TermV t) v -> Pos -> Maybe (UTerm (TermV t) v)
termAtPosV t [] = Just $ t 
termAtPosV t (n:ps) = let args = argumentsV t in
  if (length args < n && n > 0) then Nothing else termAtPosV ((argumentsV t)!!(n-1)) ps

symbolAtPosV :: UTerm (TermV t) v -> Pos -> Maybe t
symbolAtPosV t [] = case rootV t of
  Right f -> Just f
  Left _ -> Nothing
symbolAtPosV t (n:ps) = let args = argumentsV t in
  if (length args < n && n > 0) then Nothing else symbolAtPosV ((argumentsV t)!!(n-1)) ps

posTermV :: UTerm (TermV t) v -> UTerm (TermV Pos) v
posTermV t = treeToTermV [] $ map (positions []) $ zip (argumentsV t) [1..] where
  positions p (ti, i) = let pi = p ++ [i] in treeToTermV pi $ map (positions pi) $ zip (argumentsV ti) [1..]

mapTermV :: (t -> t') -> UTerm (TermV t) v -> UTerm (TermV t') v
mapTermV f (UVar x) = UVar x
mapTermV f (UTerm (SymbolV s)) = UTerm $ SymbolV $ f s
mapTermV f (UTerm (AppV l r)) = UTerm $ AppV (mapTermV f l) (mapTermV f r)

mapOverPosV :: (Pos -> Maybe t') -> UTerm (TermV t) v -> Maybe (UTerm (TermV t') v)
mapOverPosV f t = noNothing $ mapTermV f $ posTermV t where
  noNothing (UVar x) = Just $ UVar x
  noNothing (UTerm (SymbolV (Just s))) = Just $ UTerm $ SymbolV $ s
  noNothing (UTerm (SymbolV Nothing)) = Nothing
  noNothing (UTerm (AppV l r)) = do
    l' <- noNothing l
    r' <- noNothing r
    return $ UTerm $ AppV l' r'

substituteAtPosV :: UTerm (TermV t) v -> UTerm (TermV t) v -> Pos -> Maybe (UTerm (TermV t) v)
substituteAtPosV t t' [] = Just t'
substituteAtPosV t t' (p : ps) = do
    guard $ length args < p && p > 0
    r <- s
    args' <- sequence $ applyAt (p-1) (\x -> substituteAtPosV x t' ps) args
    return $ treeToTermV r args'
  where args = argumentsV t
        s = case rootV t of
          Left v -> Nothing
          Right s' -> Just s'
        applyAt _ f [] = [Nothing]
        applyAt 0 f (l : ls) = (f l) : map Just ls
        applyAt n f (l : ls) = (Just l) : applyAt (n-1) f ls


depthV :: UTerm (TermV t) v -> Int
depthV = maximum . (map length) . posV

{-
nubByTerms removes duplicates from a list of terms and returns the result list in a BindingMonad
-}
nubByTerms :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
               [UTerm (TermV t) v] -> em m [UTerm (TermV t) v]
nubByTerms [] = return []
nubByTerms (t:ts) = fmap (t:) $ (nubByTerms ts) >>= filterM (lift . fmap not . equals t)

{-
elemByTerms' tests if a term is an element of a list of terms.
-}
elemByTerms' :: UTerm (TermV String) IntVar -> [UTerm (TermV String) IntVar] -> Bool
elemByTerms' _ [] = False
elemByTerms' t' (t:ts) = (runIdentity $ evalIntBindingT (equals t' t)) || (elemByTerms' t' ts)

{-
lpo is a lexicographic path ordering on terms >_lpo
-}
lpoV :: (Ord t, Eq v) => UTerm (TermV t) v -> UTerm (TermV t) v -> Bool
lpoV (UVar s) (UVar t) = s /= t  --s >_lpo t iff
lpoV (UVar _) (UTerm _) = False
lpoV (UTerm _) (UVar _) = True --t is a variable and s /= t or
lpoV (UTerm (SymbolV f)) (UTerm (SymbolV g)) = f > g --constants are compared by the order on the signature
lpoV s t = a || b || c where
  a = (or $ map (\i -> lpoV i t) si) || (or $ map (\i -> eqUTerm i t) si)
  b = (f > g) && (and $ map (lpoV s) ti)
  c = (f == g) && case findIndex (not) $ zipWith eqUTerm si ti of
    Nothing -> False
    Just i -> (lpoV (si !! i) (ti !! i)) && (and $ map (lpoV s) $ drop (i+1) ti)
  f = rootV' s
  g = rootV' t
  si = argumentsV s
  ti = argumentsV t
  rootV' (UTerm (SymbolV x)) = x
  rootV' (UTerm (AppV l r)) = rootV' l

