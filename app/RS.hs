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
type RS t v = [(UTerm (Term t) v, UTerm (Term t) v)]

{-
symbols returns all symbols of a term.
We assume that application is left-associative and therefor the "root-symbol" of a term is in the
"left-most" leaf.
-}
symbolsOf :: Eq t => RS t v -> [(t, Int)]
symbolsOf [] = []
symbolsOf ((t, t'):ts) = nub $ findSymbols t ++ findSymbols t' ++ symbolsOf ts {-where
  findSymbols (UVar _) = []
  findSymbols (UTerm (Symbol f)) = [(f, 0)]
  findSymbols (UTerm (App l r)) = case symbol l of
    Just s -> let args = arguments (UTerm (App l r)) in [(s, length $ args)] ++ (args >>= findSymbols)
    Nothing -> []
  symbol (UVar _) = Nothing
  symbol (UTerm (Symbol f)) = Just f
  symbol (UTerm (App (UTerm (Symbol f)) r)) = Just f
  symbol (UTerm (App l r)) = symbol l-}

{-
l is the list of left-hand sides of a rewriting system
-}
l :: RS t v -> [UTerm (Term t) v]
l = map fst

{-
l1 is the subset of linear subterms of l, but is constructed directly from a rewriting system
-}
l1 :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
       RS t v -> em m [UTerm (Term t) v]
l1 = return . filter (isLinear) . l

{-
l2 is the linearization of the non-linear terms in l, constructed directly from a rewriting system
l2 returns pairs (non-linearized terms, linearized term), such that we have the non-linearized terms
available for the computation of the transition relation of the ADC.
-}
l2 :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
       RS t v -> em m [(UTerm (Term t) v, UTerm (Term t) v)] --[UTerm (Term t) v]
l2 x = do --(return $ filter (not . isLinear) $ l x) >>= nubByTerms >>= mapM linearize
  nlins <- (return $ filter (not . isLinear) $ l x) >>= nubByTerms
  lins <- return nlins >>=  mapM linearize
  return $ zip nlins lins
  


