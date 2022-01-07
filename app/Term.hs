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
Simple Termalgebra that supports unification-fd
-}
data Term t v = Symbol !t | App !v !v deriving (Show, Eq, Ord, Traversable, Functor, Foldable)

instance Eq t => Unifiable (Term t) where
  zipMatch (Symbol x) (Symbol y) | (x == y) = Just (Symbol x)
  zipMatch (App l1 r1) (App l2 r2) = Just (App (Right (l1,l2)) (Right (r1,r2)))
  zipMatch _ _ = Nothing

{-
Concrete BindingMonad instance for computations over terms
-}
type BspFailure =  UFailure (Term String) IntVar
type FallibleBindingMonad = ExceptT BspFailure (IntBindingT (Term String) Identity)

runFBM :: FallibleBindingMonad a -> (Either BspFailure a, IntBindingState (Term String))
runFBM = runIdentity . runIntBindingT . runExceptT

evalFBM :: FallibleBindingMonad a -> Either BspFailure a
evalFBM = runIdentity . evalIntBindingT . runExceptT

execFBM :: FallibleBindingMonad a -> IntBindingState (Term String)
execFBM = runIdentity . execIntBindingT . runExceptT

{-
linearize returns the linearization of the input term
-}
linearize :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
              UTerm (Term t) v -> em m (UTerm (Term t) v)
linearize (UTerm (Symbol x)) = return . UTerm $ Symbol x
linearize (UTerm (App l r)) = do
  l' <- linearize l
  r' <- linearize r
  return . UTerm $ App l' r'
linearize (UVar _) = fmap UVar $ lift freeVar


{-
isLinear tests if a given term is linear
-}
isLinearInCtxt :: Eq v => UTerm (Term t) v -> [v] -> (Bool, [v])
isLinearInCtxt (UTerm (Symbol x)) ctxt = (True, ctxt)
isLinearInCtxt (UTerm (App l r)) ctxt = let le = (isLinearInCtxt l ctxt)  in
  let re = (isLinearInCtxt r (snd le)) in
    ((fst le) && (fst re), snd re)
isLinearInCtxt (UVar x) ctxt = if (elem x ctxt) then (False, ctxt) else (True, x : ctxt)

isLinear :: Eq v => UTerm (Term t) v -> Bool
isLinear = fst . (flip isLinearInCtxt [])

{-
some helper functions on terms
-}
arguments :: UTerm (Term t) v -> [UTerm (Term t) v]
arguments (UTerm (Symbol _)) = []
arguments (UTerm (App (UTerm (Symbol f)) r)) = [r]
arguments (UTerm (App l r)) = arguments' l [r] where
  arguments' (UTerm (App (UTerm (Symbol f)) r)) s = r : s
  arguments' (UTerm (App l r)) s = arguments' l (arguments' r s)
  arguments' x s = x : s

root :: UTerm (Term t) v -> Either v t
root (UVar v) = Left v
root (UTerm (Symbol f)) = Right f
root (UTerm (App l r)) = root l

findSymbols :: Eq t => UTerm (Term t) v -> [(t, Int)]
findSymbols (UVar _) = []
findSymbols (UTerm (Symbol f)) = [(f, 0)]
findSymbols (UTerm (App l r)) = nub $ case root l of
    Right s -> let args = arguments (UTerm (App l r)) in [(s, length $ args)] ++ (args >>= findSymbols)
    Left _ -> []


treeToTerm :: t -> [UTerm (Term t) v] -> UTerm (Term t) v
treeToTerm f args = foldl (\t t' -> UTerm $ App t t') (UTerm (Symbol f)) args

{-
subTerms computes the list of all subterms of a given term
-}
subTerms :: UTerm (Term t) v -> [UTerm (Term t) v]
subTerms (UVar x) = [UVar x]
subTerms (UTerm (Symbol x)) = [UTerm $ Symbol x]
subTerms t = (t:) $ (arguments t >>= subTerms)

{-
strictSubTerms computes the list of all strict subterms of a given term
-}
strictSubTerms :: UTerm (Term t) v -> [UTerm (Term t) v]
strictSubTerms (UVar x) = []
strictSubTerms t = arguments t >>= subTerms


type Pos = [Int] 
{-
vars returns all variable of a term together with their position.
If a variable occurs in multiple positions, it occurs multiple times in the result.
-}
vars :: UTerm (Term t) v -> [(v, Pos)]
vars (UVar x) = [(x, [])]
vars (UTerm (Symbol _)) = []
vars t = vars' $ zip (arguments t) [1..] where
  vars' [] = []
  vars' ((t,n) : ps) = (map (\(v,ns) -> (v, n:ns)) (vars t)) ++ vars' ps

{-
pos returns the list of all positions of a Term
-}
pos :: UTerm (Term t) v -> [Pos]
pos (UVar _) = [[]]
pos (UTerm (Symbol _)) = [[]]
pos t = pos' $ zip (arguments t) [1..] where
  pos' [] = [[]]
  pos' ((t,n) : ps) = (map (\ns -> n:ns) (pos t)) ++ pos' ps

termAtPos :: UTerm (Term t) v -> Pos -> Maybe (UTerm (Term t) v)
termAtPos t [] = Just $ t 
termAtPos t (n:ps) = let args = arguments t in
  if (length args < n && n > 0) then Nothing else termAtPos ((arguments t)!!(n-1)) ps

symbolAtPos :: UTerm (Term t) v -> Pos -> Maybe t
symbolAtPos t [] = case root t of
  Right f -> Just f
  Left _ -> Nothing
symbolAtPos t (n:ps) = let args = arguments t in
  if (length args < n && n > 0) then Nothing else symbolAtPos ((arguments t)!!(n-1)) ps

posTerm :: UTerm (Term t) v -> UTerm (Term Pos) v
posTerm t = treeToTerm [] $ map (positions []) $ zip (arguments t) [1..] where
  positions p (ti, i) = let pi = p ++ [i] in treeToTerm pi $ map (positions pi) $ zip (arguments ti) [1..]

mapTerm :: (t -> t') -> UTerm (Term t) v -> UTerm (Term t') v
mapTerm f (UVar x) = UVar x
mapTerm f (UTerm (Symbol s)) = UTerm $ Symbol $ f s
mapTerm f (UTerm (App l r)) = UTerm $ App (mapTerm f l) (mapTerm f r)

mapOverPos :: (Pos -> Maybe t') -> UTerm (Term t) v -> Maybe (UTerm (Term t') v)
mapOverPos f t = noNothing $ mapTerm f $ posTerm t where
  noNothing (UVar x) = Just $ UVar x
  noNothing (UTerm (Symbol (Just s))) = Just $ UTerm $ Symbol $ s
  noNothing (UTerm (Symbol Nothing)) = Nothing
  noNothing (UTerm (App l r)) = do
    l' <- noNothing l
    r' <- noNothing r
    return $ UTerm $ App l' r'

substituteAtPos :: UTerm (Term t) v -> UTerm (Term t) v -> Pos -> Maybe (UTerm (Term t) v)
substituteAtPos t t' [] = Just t'
substituteAtPos t t' (p : ps) = do
    guard $ length args < p && p > 0
    r <- s
    args' <- sequence $ applyAt (p-1) (\x -> substituteAtPos x t' ps) args
    return $ treeToTerm r args'
  where args = arguments t
        s = case root t of
          Left v -> Nothing
          Right s' -> Just s'
        applyAt _ f [] = [Nothing]
        applyAt 0 f (l : ls) = (f l) : map Just ls
        applyAt n f (l : ls) = (Just l) : applyAt (n-1) f ls


depth :: UTerm (Term t) v -> Int
depth = maximum . (map length) . pos
{-
nubByTerms removes duplicates from a list of terms and returns the result list in a BindingMonad
-}
nubByTerms :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
               [UTerm (Term t) v] -> em m [UTerm (Term t) v]
nubByTerms [] = return []
nubByTerms (t:ts) = fmap (t:) $ (nubByTerms ts) >>= filterM (lift . fmap not . equals t)

{-
elemByTerms' tests if a term is an element of a list of terms.
-}
elemByTerms' :: UTerm (Term String) IntVar -> [UTerm (Term String) IntVar] -> Bool
elemByTerms' _ [] = False
elemByTerms' t' (t:ts) = (runIdentity $ evalIntBindingT (equals t' t)) || (elemByTerms' t' ts)

eqUTerm :: (Eq t, Eq v) => UTerm (Term t) v -> UTerm (Term t) v -> Bool
eqUTerm (UVar x) (UVar y) = x == y
eqUTerm (UTerm (Symbol f)) (UTerm (Symbol g)) = f == g
eqUTerm (UTerm (App l r)) (UTerm (App l' r')) = eqUTerm l l' && eqUTerm r r'
eqUTerm _ _ = False

{-
lpo is a lexicographic path ordering on terms >_lpo
-}
lpo :: (Ord t, Eq v) => UTerm (Term t) v -> UTerm (Term t) v -> Bool
lpo (UVar s) (UVar t) = s /= t  --s >_lpo t iff
lpo (UVar _) (UTerm _) = False
lpo (UTerm _) (UVar _) = True --t is a variable and s /= t or
lpo (UTerm (Symbol f)) (UTerm (Symbol g)) = f > g --constants are compared by the order on the signature
lpo s t = a || b || c where
  a = (or $ map (\i -> lpo i t) si) || (or $ map (\i -> eqUTerm i t) si)
  b = (f > g) && (and $ map (lpo s) ti)
  c = (f == g) && case findIndex (not) $ zipWith eqUTerm si ti of
    Nothing -> False
    Just i -> (lpo (si !! i) (ti !! i)) && (and $ map (lpo s) $ drop (i+1) ti)
  f = root' s
  g = root' t
  si = arguments s
  ti = arguments t
  root' (UTerm (Symbol x)) = x
  root' (UTerm (App l r)) = root' l

instance (Eq t, Eq v) => Eq (UTerm (Term t) v) where
  (==) = eqUTerm


leqUTerm :: (Ord t, Eq v) => UTerm (Term t) v -> UTerm (Term t) v -> Bool
leqUTerm (UVar x) (UVar y) = x == y
leqUTerm (UTerm (Symbol f)) (UTerm (Symbol g)) = f <= g
leqUTerm (UTerm (App l r)) (UTerm (App l' r')) = leqUTerm l l' && leqUTerm r r'
leqUTerm _ _ = False

instance (Ord t, Eq v) => Ord (UTerm (Term t) v) where
  l <= r = leqUTerm r l
