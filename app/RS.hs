{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}


module RS where
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
import Term

{-
Rewriting Systems as tuples of terms
-}
data RS t v = RS
  { symbolsOf :: [(t, Int)] --to name the destructor for the signature this way makes refactoring easier
  , rRules :: [(UTerm (TermV t) v, UTerm (TermV t) v)]
  } deriving Show

{-
leftHandSides is the list of left-hand sides of a rewriting system
-}
leftHandSides :: RS t v -> [UTerm (TermV t) v]
leftHandSides = map fst . rRules

{-
linearLeftHandSides is the set of linear left-hand sides of the rewriting system
-}
linearLeftHandSides :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
       RS t v -> em m [UTerm (TermV t) v]
linearLeftHandSides = return . filter (isLinear) . leftHandSides

{-
linearizationsOfNonlinearLeftHandSides is the linearization of the
non-linear terms in l, constructed directly from a rewriting system

linearizationsOfNonlinearLeftHandSides returns pairs (non-linearized
terms, linearized term), such that we have the non-linearized terms
available for the computation of the transition relation of the ADC.
-}

linearizationsOfNonlinearLeftHandSides :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
       RS t v -> em m [(UTerm (TermV t) v, UTerm (TermV t) v)] --[UTerm (Term t) v]
linearizationsOfNonlinearLeftHandSides x = do
  nlins <- (return $ filter (not . isLinear) $ leftHandSides x) >>= nubByTerms
  lins <- return nlins >>=  mapM linearize
  return $ zip nlins lins
