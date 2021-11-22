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
data Term t v = Symbol t | App v v deriving (Show, Eq, Traversable, Functor, Foldable)

instance Eq t => Unifiable (Term t) where
  zipMatch (Symbol x) (Symbol y) | (x == y) = Just (Symbol x)
  zipMatch (App l1 r1) (App l2 r2) = Just (App (Right (l1,l2)) (Right (r1,r2)))
  zipMatch _ _ = Nothing

type BspFailure =  UFailure (Term String) IntVar
type FallibleBindingMonad = ExceptT BspFailure (IntBindingT (Term String) Identity)

runFBM :: FallibleBindingMonad a -> (Either BspFailure a, IntBindingState (Term String))
runFBM = runIdentity . runIntBindingT . runExceptT

evalFBM :: FallibleBindingMonad a -> Either BspFailure a
evalFBM = runIdentity . evalIntBindingT . runExceptT

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
subTerms computes the list of all subterms of a given term
-}
arguments :: UTerm (Term t) v -> [UTerm (Term t) v]
arguments (UTerm (App (UTerm (Symbol f)) r)) = [r]
arguments (UTerm (App l r)) = arguments l ++ [r]
arguments x = [x]

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

{-
vars returns all variable of a term together with their position.
If a variable occurs in multiple positions, it occurs multiple times in the result.
-}
vars :: UTerm (Term t) v -> [(v, [Int])]
vars (UVar x) = [(x, [])]
vars (UTerm (Symbol _)) = []
vars t = vars' $ zip (arguments t) [1..] where
  vars' [] = []
  vars' ((t,n) : ps) = (map (\(v,ns) -> (v, n:ns)) (vars t)) ++ vars' ps

{-
nubByTerms removes duplicates from a list of terms and returns the result list in a BindingMonad
-}
nubByTerms :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
               [UTerm (Term t) v] -> em m [UTerm (Term t) v]
nubByTerms [] = return []
nubByTerms (t:ts) = fmap (t:) $ (nubByTerms ts) >>= filterM (lift . fmap not . equals t)

{-
elemByTerms tests if a term is an element of a list of terms
-}
elemByTerms' :: UTerm (Term String) IntVar -> [UTerm (Term String) IntVar] -> Bool
elemByTerms' _ [] = False
elemByTerms' t' (t:ts) = (runIdentity $ evalIntBindingT (equals t' t)) || (elemByTerms' t' ts)
