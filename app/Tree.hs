{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Tree where
import Control.Unification
import Data.Functor.Fixedpoint
import Control.Unification.IntVar
import Data.Maybe
import Control.Monad
import Data.List

{-
Tree Grammars as lists of rules.
Each rule is either a combinator or an applikation.
A rule Combinator "a -> a" "id" can be read as a terminal with name "id" and a
type (nonterminal) "a -> a".
A rule Apply "b" "a -> b" "a" can be read as "you obtain something of sort b from
applying something of type a -> b to something of sort a".
-}
data Rule t nt = Combinator nt t | Apply nt nt nt deriving (Show, Eq)

type TreeGrammar t nt = [Rule t nt]

{-
Simple Termalgebra that supports unification-fd
-}
data Term t v = Symbol t | App v v deriving (Show, Eq, Traversable, Functor, Foldable)

instance Eq t => Unifiable (Term t) where
  zipMatch (Symbol x) (Symbol y) | (x == y) = Just (Symbol x)
  zipMatch (App l1 r1) (App l2 r2) = Just (App (Right (l1,l2)) (Right (r1,r2)))
  zipMatch _ _ = Nothing

type PureTerm t = Fix (Term t)

{-
Rewriting Systems as tuples of terms
-}
type RS t v = [(UTerm (Term t) v, UTerm (Term t) v)]

{-
Examples for tree trammars and terms
-}
bspGr :: TreeGrammar String String
bspGr = [Combinator "a -> a" "id", Apply "a" "a -> a" "a", Combinator "a" "x"]

bspT :: UTerm (Term String) IntVar
bspT = UTerm $ App (UTerm (App (UTerm (Symbol "f")) (UVar (IntVar 0)))) (UVar (IntVar 0))

{-
Our aim is to define a function isFinite ts rs, that tests whether the intersection of
the language of a tree grammer ts and the normal forms of a rewriting systems rs is finite.
-}
isFinite :: TreeGrammar t nt -> RS t v -> Bool
isFinite tg rs = let nfAt = constructNFautomaton rs in True

{-
Finite Tree Automata with disequality constraints (ADC) as triples
([states], [final states], [transitions])
-}
data Transition q t = Transition
  { symbol :: t
  , fromState :: Maybe (q, q)
  , target :: q
  , dConstraint :: Bool
  }
  
data ADC q t = ADC
  { states :: [q]
  , final :: [q]
  , transitions :: [Transition q t]
  }

{-
linearize returns the linearization of the input term
-}
linearize :: BindingMonad (Term t) v m => UTerm (Term t) v -> m (UTerm (Term t) v)
linearize (UTerm (Symbol x)) = return . UTerm $ Symbol x
linearize (UTerm (App l r)) = do
  l' <- linearize l
  r' <- linearize r
  return . UTerm $ App l' r'
linearize (UVar _) = fmap UVar freeVar

{-
isLinear tests if a given term is linear
-}
isLinear :: BindingMonad (Term t) v m => UTerm (Term t) v  -> m Bool
isLinear (UTerm (Symbol x)) = return True
isLinear (UTerm (App l r)) = do
  l' <- isLinear l
  r' <- isLinear r
  return $ l' && r'
isLinear (UVar x) = do
  lk <- lookupVar x
  if isNothing lk then do
    y <- freeVar
    bindVar x (UVar y)
    return True
  else return False

{-
subTerms computes the list of all subterms of a given term
-}
subTerms :: UTerm (Term t) v -> [UTerm (Term t) v]
subTerms (UTerm (App l r)) = (UTerm (App l r)) : (subTerms l) ++ (subTerms r)
subTerms x = return x

{-
strictSubTerms computes the list of all strict subterms of a given term
-}
strictSubTerms :: UTerm (Term t) v -> [UTerm (Term t) v]
strictSubTerms (UTerm (App l r)) = subTerms l ++ subTerms r
strictSubTerms _ = []

data Q0 t v = AcceptAll | AcceptOnlyReducible | Q (UTerm (Term t) v) deriving Show

{-
l is the list of left-hand sides of a rewriting system
-}
l :: RS t v -> [UTerm (Term t) v]
l = map fst

{-
l1 is the subset of linear subterms of l, but is constructed directly from a rewriting system
-}
l1 :: BindingMonad (Term t) v m => RS t v -> m [UTerm (Term t) v]
l1 = filterM isLinear . l

{-
l2 is the linearization of the non-linear terms in l, constructed directly from a rewriting system
-}
l2 :: BindingMonad (Term t) v m => RS t v -> m [UTerm (Term t) v]
l2 x = (filterM (fmap not . isLinear) $ l x) >>= nubByTerms >>= mapM linearize

{-
nubByTerms removes duplicates from a list of terms and returns the result list in a BindingMonad
-}
nubByTerms :: BindingMonad (Term t) v m => [UTerm (Term t) v] -> m [UTerm (Term t) v]
nubByTerms [] = return []
nubByTerms (t:ts) = fmap (t:) $ (nubByTerms ts) >>= filterM (fmap not . equals t)

{-
(q0 r) is the list of all strict subterms of terms in the union of l1 and l2 (modulo renaming of variables)
for a rewriting system r, plus two special states:
- AcceptAll which will accept all terms
- AcceptOnlyReducible which will accept only reducible terms of r
-}
q0 :: (Eq t, Eq v, BindingMonad (Term t) v m) => RS t v -> m ([Q0 t v])
q0 r = do
  lin <- l1 r
  nlin <- l2 r
  nubbed <- nubByTerms $ (lin >>= strictSubTerms) ++ (nlin >>= strictSubTerms)
  return $ AcceptAll : AcceptOnlyReducible : (map Q nubbed)

{-
Construct an ADC from a rewriting system
(Phase 2 of Lukasz algorithm)
-}
constructNFautomaton :: RS t v -> ()
constructNFautomaton _ = () 
