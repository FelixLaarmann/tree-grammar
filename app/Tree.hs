{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}


module Tree where
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
Examples for tree trammars, terms and rewriting systems
-}
bspGr :: TreeGrammar String String
bspGr = [Combinator "a -> a" "id", Apply "a" "a -> a" "a", Combinator "a" "x"]

bspT :: UTerm (Term String) IntVar
bspT = UTerm $ App (UTerm (App (UTerm (Symbol "f")) (UVar (IntVar 0)))) (UVar (IntVar 1))

bspT' :: UTerm (Term String) IntVar
bspT' = UTerm $ App (UTerm (Symbol "x")) (UVar (IntVar 0))

bspT'' :: UTerm (Term String) IntVar
bspT'' = UTerm $ App (UVar $ IntVar 1) (UVar $ IntVar 0)

acceptAll :: UTerm (Term String) IntVar
acceptAll = UVar $ IntVar 0

terms = [bspT, bspT', bspT'', acceptAll]


{-
Example from Lukasz slides (Pres01, slide 21)
x -> 0
y -> 1
a -> 2
b -> 3
c -> 4
-}

exampleRS :: RS String IntVar
exampleRS = [(UTerm $ App (UTerm (App (UTerm $ Symbol "f") (UVar $ IntVar 0))) (UVar $ IntVar 0),
              UVar $ IntVar 2),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)) (UVar $ IntVar 2))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 3)) (UVar $ IntVar 1)),
              UVar $ IntVar 4)]

-- Maybe this could be faster than subsequences? If at some point in time the performance would matter :D
powerSetList :: [a] -> [[a]]
powerSetList = filterM $ (const [True, False])

bspRS :: RS String IntVar
bspRS = [(bspT, bspT)]

type BspFailure =  UFailure (Term String) IntVar
type FallibleBindingMonad = ExceptT BspFailure (IntBindingT (Term String) Identity)

runFBM :: FallibleBindingMonad a -> (Either BspFailure a, IntBindingState (Term String))
runFBM = runIdentity . runIntBindingT . runExceptT

evalFBM :: FallibleBindingMonad a -> Either BspFailure a
evalFBM = runIdentity . evalIntBindingT . runExceptT

{-
Our aim is to define a function isFinite ts rs, that tests whether the intersection of
the language of a tree grammer ts and the normal forms of a rewriting systems rs is finite.

isFinite :: TreeGrammar t nt -> RS t v -> Bool
isFinite tg rs = let nfAt = constructNFautomaton rs in True
-}

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
linearize (UVar x) = do
  y <- freeVar
  bindVar y (UVar x)
  return $ UVar y
-}

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

isLinearInCtxt :: Eq v => UTerm (Term t) v -> [v] -> (Bool, [v])
isLinearInCtxt (UTerm (Symbol x)) ctxt = (True, ctxt)
isLinearInCtxt (UTerm (App l r)) ctxt = let le = (isLinearInCtxt l ctxt)  in
  let re = (isLinearInCtxt r (snd le)) in
    ((fst le) && (fst re), snd re)
isLinearInCtxt (UVar x) ctxt = if (elem x ctxt) then (False, ctxt) else (True, x : ctxt)


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

data Q0 t v =  AcceptOnlyReducible | Q (UTerm (Term t) v) deriving (Show)

{-
l is the list of left-hand sides of a rewriting system
-}
l :: RS t v -> [UTerm (Term t) v]
l = map fst


{-
l1 is the subset of linear subterms of l, but is constructed directly from a rewriting system
-}
l1 :: (BindingMonad (Term t) v m, Eq v) => RS t v -> m [UTerm (Term t) v]
--l1 = filterM isLinear . l
l1 = return . filter (fst . flip isLinearInCtxt []) . l

{-
l2 is the linearization of the non-linear terms in l, constructed directly from a rewriting system
-}
l2 :: BindingMonad (Term t) v m => RS t v -> m [UTerm (Term t) v]
--l2 x = (filterM (fmap not . isLinear) $ l x) >>= nubByTerms >>= mapM linearize
l2 x = (return $ filter (not . fst . flip isLinearInCtxt []) $ l x) >>= nubByTerms >>= mapM linearize

{-
nubByTerms removes duplicates from a list of terms and returns the result list in a BindingMonad
-}
nubByTerms :: BindingMonad (Term t) v m => [UTerm (Term t) v] -> m [UTerm (Term t) v]
nubByTerms [] = return []
nubByTerms (t:ts) = fmap (t:) $ (nubByTerms ts) >>= filterM (fmap not . equals t)

{-
(q0 r) is the list of all strict subterms of terms in the union of l1 and l2 (modulo renaming of variables)
for a rewriting system r, plus two special states:
- fresh variable x, which will accept all terms
- AcceptOnlyReducible which will accept only reducible terms of r 
-}
q0withoutAOR :: (Eq t, Eq v, BindingMonad (Term t) v m) => RS t v -> m ([UTerm (Term t) v])
q0withoutAOR r = do
  lin <- l1 r
  nlin <- l2 r
  nubbed <- nubByTerms $ (lin >>= strictSubTerms) ++ (nlin >>= strictSubTerms)
  x <- freeVar
  return $ (UVar x) : nubbed

q0 :: (Eq t, Eq v, BindingMonad (Term t) v m) => RS t v -> m ([Q0 t v])
q0 r = do
  q0wQr <- q0withoutAOR r
  return $ AcceptOnlyReducible : (map Q q0wQr)

{-
To avoid that ghc complains about e being ambiguous, unifiableList must be split up into two functions.
-}

unifiableList' :: (BindingMonad (Term t) v m, Fallible (Term t) v (UFailure (Term t) v)) =>
  [UTerm (Term t) v] -> m [Either (UFailure (Term t) v) (UTerm (Term t) v)]
unifiableList' [] = return []
unifiableList' (t:ts) =  do
  l <- sequence $ map (\x -> runExceptT $ unify x t) ts
  r <- unifiableList' ts
  return $ l ++ r

unifiableList'' :: (BindingMonad (Term t) v m, Fallible (Term t) v (UFailure (Term t) v)) =>
  m [Either (UFailure (Term t) v) (UTerm (Term t) v)] -> m Bool
unifiableList'' ls = do
  l <- ls
  return $ and $ map isRight l


{-
unifiableList :: (BindingMonad (Term t) v m, Fallible (Term t) v e) =>
  [UTerm (Term t) v] -> m Bool
unifiableList [] = return True
unifiableList (t:ts) = do
  l <- sequence $ map (\x -> (runExceptT $ unify x t) >>= return . isRight) ts
  b <- unifiableList ts
  return $ (and l) && b
-}

{-
Computes the powerset modulo unification from a set/list of terms
-}
unifiableSubsets :: (BindingMonad (Term t) v m) => [UTerm (Term t) v] -> m[[UTerm (Term t) v]]
unifiableSubsets  = (filterM (unifiableList'' . unifiableList')) . subsequences

mgu :: (BindingMonad (Term t) v m, Fallible (Term t) v e) =>
  [UTerm (Term t) v] -> ExceptT e m (UTerm (Term t) v)
mgu (t:[]) = return t
mgu (t1:t2:ts) = do {
  u1 <- unify t1 t2;
  u2 <- mgu (t2:ts);
  unify u1 u2
  }

mguSubsets' :: (BindingMonad (Term t) v m, Fallible (Term t) v e) => [UTerm (Term t) v] -> --[ExceptT e m (UTerm (Term t) v)]
  [m (Either e  (UTerm (Term t) v))]
mguSubsets' = (map runExceptT) . (map (mgu)) . (filter (not . null)) . subsequences

mguSubsets'' :: (BindingMonad (Term t) v m, MonadPlus m, Fallible (Term t) v e) => [m (Either e (UTerm (Term t) v))] -> [m (UTerm (Term t) v)]
mguSubsets'' = map $ (\x -> x >>= either (\_ -> mzero) (return))



{-
deltaR :: (Eq t, Eq v, BindingMonad (Term t) v m) => RS t v -> m [Transition (UTerm (Term t) v) t]
deltaR rs = do
  f <- first
  s <- second
  return $ f ++ s where
    first = do
      candidate <- l1 rs
      q0w <- q0withoutAOR rs
      qr <- unifiableSubsets q0w
      mgus <- mgu qr
      return  []
    second = return []
-}

{-
Construct an ADC from a rewriting system
(Phase 2 of Lukasz algorithm)
-}
constructNFautomaton :: RS t v -> ()
constructNFautomaton _ = () 

