{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}


module ADC where
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
import Prelude hiding (pi)
import qualified Data.MultiSet as MultiSet
import qualified Data.Map as Map
import qualified Data.Set as Set

import Term
import RS
import Grammar

{-
Finite Tree Automata with disequality constraints (ADC) as triples
([states], [final states], [transitions])

For CLS only nullary or binary domains of transitions are possible.
-}

data Transition q t = Transition
  { symbol :: !t
  , fromState :: ![q]
  , target :: !q
  , dConstraint :: ![[(Pos, Pos)]]--Bool --better [[(pos, pos)]] because this is a formula (conjunction of disjunctions of disequalities)
  -- Top is []
  } deriving (Show, Eq, Ord)

data ADC q t = ADC
  { states :: ![q]
  , final :: ![q]
  , transitions :: ![Transition q t]
  } deriving Show


prettyPrintADC :: (Show t, Show v) => ADC t v -> IO()
prettyPrintADC adc = do
  putStrLn "\n##### States #####\n"
  mapM_ print $ states adc
  putStrLn "\n\n\n##### Final States #####\n"
  mapM_ print $ final adc
  putStrLn "\n\n\n##### Transitions #####\n"
  mapM_ print $ transitions adc

{- Are disequality constraints satisfied? -}
satisfies :: (Eq t) => Term t -> [[(Pos, Pos)]] -> Bool
satisfies t conjunction = and $ map (satisfiesDisjunction t) conjunction where
  satisfiesDisjunction t disjunction = or $ map (satisfiesDisEq t) disjunction
  satisfiesDisEq :: (Eq t) => Term t -> (Pos, Pos) -> Bool
  satisfiesDisEq t (p1,p2) = not $
      case t `termAtPos` p1 of
        Just tp1 -> case t `termAtPos` p2 of
          Just tp2 -> tp1 == tp2
          Nothing -> False
        Nothing -> False

{-
modSym computes a relation modulo symmetry
-}
modSym :: Eq a => [(a,a)] -> [(a,a)]
modSym [] = []
modSym ((a,b):ls) = (a,b) : (modSym $ filter (/= (b,a)) ls)


{-
atoms returns the list of all distinct disequalities from the transitions of an ADC.
-}
atoms :: ADC q t -> [(Pos, Pos)]
atoms = modSym . nub . join . join . (map dConstraint) . transitions

{-
c(ADC) computes the number of all distinct triples (??,??,?????) such that ?? is a prefix of
?????and ????=????? or ???????=?? is an atom occurring in a constraint of transition rules of ADC.
-}
c :: ADC q t -> Int
c adc = length [(beta, pi, pi') | (pi, pi') <- pis, beta <- inits pi', beta `isPrefixOf` pi'] where
  pis = modSym $ atoms adc

{-
pi(ADC) is the maximum length of ?? in a constraint ????=????? or ???????=?? in ADC.
-}
pi :: ADC q t -> Int
pi = maximum . (0:) . (map (\(l,r) -> max (length l) (length r))) . atoms

{-
(q0 r) is the list of all strict subterms of terms in the union of l1 and l2 (modulo renaming of variables)
for a rewriting system r, plus two special states:
- fresh variable x, which will accept all terms
- AcceptOnlyReducible which will accept only reducible terms of r
-}

data Q0 t v =  AcceptOnlyReducible | Q !(UTerm (TermV t) v) deriving (Show)


instance Eq (Q0 String IntVar) where
  AcceptOnlyReducible == AcceptOnlyReducible = True
  Q t == Q t' = runIdentity $ evalIntBindingT $ t === t'
  _ == _ = False

{-
deriving instance Ord (Q0 String IntVar)
-}

q0withoutAOR :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
                 RS t v -> em m [UTerm (TermV t) v]
q0withoutAOR r = do
  lin <- linearLeftHandSides r
  nlin' <- linearizationsOfNonlinearLeftHandSides r
  let nlin = map snd nlin'
  nubbed <- nubByTerms $ (lin >>= strictSubTermsV) ++ (nlin >>= strictSubTermsV)
  --let modRenaming = filter noUVar nubbed
  modRenaming <- mapM freshen $ filter noUVar nubbed
  x <- lift freeVar
  return $ (UVar x) : modRenaming where --modulo renaming means that each variable in a set of terms has to be distinct.
    noUVar (UVar _) = False
    noUVar _ = True

q0 :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
      RS t v -> em m ([Q0 t v])
q0 r = do
  q0wQr <- q0withoutAOR r
  return $ AcceptOnlyReducible : (map Q q0wQr)

{-
mgu computes the most general unifier of a list of terms
-}
mgu :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
       [UTerm (TermV t) v] -> em m (UTerm (TermV t) v)
mgu ([]) = error "mgu of empty list"
mgu (t:[]) = return t
mgu (t1:t2:ts) = do
  u1 <- unify t1 t2
  u2 <- mgu (t2:ts)
  u <- unify u1 u2
  applyBindings u

{-
mguSubsets computes the powerset modulo unification from a set/list of terms
with the mgu to represent each subset
-}
mguSubsets :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em,
               MonadError e (em m)) =>
               [UTerm (TermV t) v] -> [em m (UTerm (TermV t) v)]
mguSubsets ts = map mgu $ filter (not . null) $ subsequences ts


mguSubsets' :: [UTerm (TermV String) IntVar] -> [UTerm (TermV String) IntVar]
mguSubsets' ts = fromErrorList $ map evalFBM $ either (\_ -> []) (\x -> x) $ evalFBM $
  (return . mguSubsets) ts where
    fromErrorList [] = []
    fromErrorList (Left e : es) = fromErrorList es
    fromErrorList (Right t : es) = t : fromErrorList es

{-
deltaR' computes the transitions for n-ary symbols.
-}
deltaR' :: RS String IntVar -> [UTerm (TermV String) IntVar]
  -> [Transition (Q0 String IntVar) String]
deltaR' rs qr = tops ++ constraints where
{-
f(q_u_1,...,q_u_n)-c???> q_u where q_u_1,...,q_u_n, q_u ??? Qr and:
-}
  symbols = symbolsOf rs
  l1s = (either (\_ -> []) (\x -> x) $ evalFBM $ linearLeftHandSides rs)
  nArySymbols = nub [(map fst $ filter ((== n) . snd) symbols, n) | (f, n) <- symbols]
  instanceOfSome t ls = filter (\x -> either (\_ -> False) (\x -> x) $ evalFBM $ (x <:= t)) ls
  fromStates n = sequence $ (take n) $ repeat qr
  fromStatesAOR n = sequence . (take n) . repeat $ AcceptOnlyReducible : (map Q qr)
  isQr AcceptOnlyReducible = True
  isQr _ = False
  tops = [Transition s args AcceptOnlyReducible []  |
          (ls, n) <- nArySymbols, s <- ls, args <- fromStatesAOR n, or $ map isQr args] ++
         --if (at least???) one of the q_u_i???s is q_r
         [Transition s (map Q args) AcceptOnlyReducible []  |
          (ls, n) <- nArySymbols, s <- ls, args <- fromStates n,
          not $ null $ instanceOfSome (treeToTermV s args) l1s]
         --or f(u_1,...,u_n) is an instance of some s??? L1, then q_u=q_r and c=???
  q0without = either (\_ -> []) (\x -> x) $ evalFBM $ q0withoutAOR rs
  constraints = do
    (ls, n) <- nArySymbols
    s <- ls
    args <- fromStates n
    guard $ null $ instanceOfSome (treeToTermV s args) l1s
    case (evalFBM $ mgu $
          instanceOfSome (treeToTermV s args) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return $ Transition s (map Q args) (Q $ u) form where
          form = do
            l <- either (\_ -> []) (\x -> x) $ evalFBM $ linearizationsOfNonlinearLeftHandSides rs
            --l is a pair of the prelinearized and the linearized terms
            guard $ isRight $ evalFBM $ unify u $ snd l --here the linearized one has to be used
            guard $ not $ null $ instanceOfSome (treeToTermV s args) [snd l] --this guard is the result of a discussion with Lukasz and has to be added in the paper
            let xs = vars $ fst l --here the prelinearized
            return $ modSym $ do
              --look up all positions, if there are for example 3 or more positions of x, all pairs p1 /= p2 have to be checked.
              (x, p1) <- xs
              (x', p2) <- filter (\p -> x == fst p) $ delete (x,p1) xs
              return (p1,p2)
      Left _ -> mzero

{-
constructNfADC' constructs an automaton with disequality constraints (ADC) from a given
rewriting system rs.
This function implements phase 2 of Lukasz algorithm.

constructNfADC' names the state "senseful" for debugging.
-}
constructNfADC' :: RS String IntVar -> ADC (Q0 String IntVar) String
constructNfADC' rs = ADC{
  states = qr,
  final = map Q qrWithout,
  transitions = deltaR' rs qrWithout
                             } where
  qrWithout = either (\_ -> []) (\x -> x) $ evalFBM $
    (q0withoutAOR rs >>= nubByTerms . mguSubsets')
  qr = either (\_ -> []) (\x -> x) $ evalFBM $
    (q0withoutAOR rs >>= nubByTerms . mguSubsets' >>=
     \q0wQr -> return $ AcceptOnlyReducible : (map Q q0wQr))

{-
constructNfADC constructs an automaton with disequality constraints (ADC) from a given
rewriting system rs.
This function implements phase 2 of Lukasz algorithm.

constructNfADC uses Int as states for better algorithmic behaviour.
-}
simplifyStates :: Eq q => ADC q t -> ADC Int t
simplifyStates adc = ADC (map snd indexed) fin trans where
  indexed = zip (states adc) [0..]
  fin = do
    qf <- final adc
    Just i <- return $ lookup qf indexed
    return i
  trans = do
    t <- transitions adc
    let from = do
          dom <- fromState t
          Just i <- return $ lookup dom indexed
          return i
    Just qt <- return $ lookup (target t) indexed
    return $ Transition (symbol t) from qt (dConstraint t)

constructNfADC :: RS String IntVar -> ADC Int String
constructNfADC = simplifyStates . constructNfADC'

{-
constructADC constructs an automaton with disequality constraints (ADC)
from a given TreeGrammar.

This function implements phase 1 of Lukasz algorithm.
-}
constructADC :: (Eq t, Eq nt,  Newable nt) => TreeGrammar t nt -> ADC nt t
constructADC g = ADC (nonTerminals g') [axiom g'] (map transition $ rules g') where
  g' = normalize g
  transition (a, Terminal f args) = Transition f (from args) a [] --partial function, because g is normalized
  from [] = []
  from (NonTerminal a : qs) = a : (from qs) --partial function, because g is normalized

{-
productADC computes the product ADC for two given ADC's.
This function implements phase 3 of Lukasz algorithm.

Note:
We assume that the symbols/terminals have the same type.
And symbols with the same "name" have the same arity.
-}
productADC :: Eq t => ADC q t -> ADC q' t -> ADC (q, q') t
productADC a1 a2 = ADC {
  states = [(q1, q2) | q1 <- states a1, q2 <- states a2],
  final = [(q1, q2) | q1 <- final a1, q2 <- final a2],
  transitions = do
      t1 <- transitions a1
      t2 <- transitions a2
      let s =  symbol t1
      guard (s == symbol t2)
      let args1 = fromState t1
      let args2 = fromState t2
      guard (length args1 == length args2)
      return $ Transition s (zip args1 args2) (target t1, target t2) (dConstraint t1 ++ dConstraint t2)
                       }

{-
Automaton heightADC = (Q_n, Q^f_n, Delta_n) recognising the language of all trees of height at least n \in Nat.
Q_n = {q} U {q_i | i \in {0,...,n}}
Q^f_n = {q_n}
Delta_n consists of all transitions
a -> q_0 (I assume that a represents all symbols with arity 0?)
f(q_i_1,..., q_i_n) -> q_min(max(i_1,...,i_n)+1, n) for n > 0 and all i_1,...i_n \in {0,...,n}
(Obviously we assume that all symbols f \in F are given, since the tree language L(G) intersect L(RS) implies that G and RS somehow uses the same signature F.
Otherwise the intersection would be emtpy, trivially :D)
-}
terminalsWithArity :: Eq t => TreeGrammar t nt -> [(t, Int)]
terminalsWithArity g = nub $ rules g >>= (arity . snd) where
  arity (Terminal t args) = (t, length args) : (args >>= arity)
  arity (NonTerminal _) = []

intersectSymbols :: Eq t => RS t v -> TreeGrammar t nt -> [(t, Int)]
intersectSymbols rs gr = intersect (terminalsWithArity gr) (symbolsOf rs)

heightADC :: Eq t => Integer -> [(t, Int)] -> ADC Integer t
heightADC n ts = ADC [0..n] [n] trans where
  trans = map (\a -> Transition a [] 0 []) nullaryTs ++
    [Transition f args (min (1 + maximum (0 : args)) n) [] |
     (ls, n') <- nArySymbols, f <- ls, args <- nAryProd n' [0..n]]
  nullaryTs = map fst $ filter ((== 0) . snd) ts
  nAryProd n = sequence . (take n) . repeat
  nArySymbols = nub [(map fst $ filter ((== n') . snd) ts, n') | (f, n') <- ts, n' > 0]

{-
[CJ03] defines the size of a term as the cardinal
|Pos(t)| of its positions set.
-}
sizeT :: UTerm (TermV t) v -> Integer
sizeT = toInteger . length . posV

{-
I'm not sure how Lukasz defines the size of a tree grammar, but usually the size
of a grammar is something like the sum of the sizes of all right-hand sides of the production rules.
-}
sizeG :: TreeGrammar t nt -> Integer
sizeG g = sum $ map (size . snd) $ rules g where
  size (Terminal _ ts) = 1 + (sum $ map size ts)
  size (NonTerminal _) = 0

{-
[CJ03] defines the size of a rewrite system R as the
sum of the sizes of its left members
-}
sizeR :: RS t v -> Integer
sizeR r = sum $ map (sizeT . fst) $ rRules r

{-
Automaton eIfIntersectionFin = A x A_n whose  language  is  empty  iff L(G)???NF(R) is finite, where A = A_G (phase 1) x A_R (phase 2)
Choose n \in Nat to be
n = (e+1) x |G| x 2^(|R|^3 +|R| + 2 ) x (|R|^3)! x |R|
where e = 2,718... is Euler's Number.

For debugging and because its interesting we return the computed n's for each transition in the first
projection
-}

eIfIntersectionFin :: (Eq nt, Newable nt) => TreeGrammar String nt -> RS String IntVar ->
  Either (ADC (nt, Int) String) (Integer, ADC ((nt, Int), Integer) String)
eIfIntersectionFin g r = if n == 0 then Left a else Right (n, productADC a (heightADC n f)) where
  a = productADC (constructADC g) (constructNfADC r)
  f = intersectSymbols r g
  n = div (371828182845 * (toInteger $ length $ states a) *
           (2^(toInteger $ c a)) * (fac $ toInteger $ c a) * (toInteger $ pi a)) 100000000000

--lists and MultiSets do not implement this for Ord
multiSetExtension :: Ord a => (a -> a -> Bool) ->  MultiSet.MultiSet a -> MultiSet.MultiSet a -> Bool
multiSetExtension ord m n = or $ do
  x' <- filter (/= []) $ subsequences $ MultiSet.elems m
  let x = MultiSet.fromList x'
  let y = MultiSet.difference n (MultiSet.difference m x)
  x'' <- x'
  return $ MultiSet.fold (\a b -> b && ord x'' a) True y

(>>>) :: (Ord t) => Term t -> Term t -> Bool
(>>>) rho1 rho2 = lexProd (depth rho1, rho1) (depth rho2, rho2) where
  lexProd (d, r) (d', r') | d == d' = r > r'
                          | otherwise = d > d'

compareTerm :: (Ord t) => Term t -> Term t -> Ordering
compareTerm t1 t2 | t1 == t2 = EQ
                  | t1 >>> t2 = GT
                  | otherwise = LT

newtype OrdTerm t = OrdTerm {getTerm :: Term t} deriving (Eq, Show)

instance Ord t => Ord (OrdTerm t) where
  compare l r = compareTerm (getTerm l) (getTerm r)

checkForSequence rho 0 p _ = True
checkForSequence rho b p [] = False
checkForSequence rho b p (r:rs) = case substituteAtPos rho r p of
      Just pump -> if (not $ containsCloseEq pump p)
        then checkForSequence rho (b-1) p rs
        else checkForSequence rho b p rs
      Nothing -> checkForSequence rho b p rs

containsCloseEq :: (Eq t, Eq q) => Term (Transition q t) -> Pos -> Bool
containsCloseEq rho p = or $ do
    let posRho = pos rho
    p' <- posRho
    guard $ p' `isPrefixOf` p -- p' <= p
    Just s <- return $ symbolAtPos rho p'
    (pi, pi') <- (nub $ join $ dConstraint s)
    let ppi = (p' ++ pi)
    let ppi' = (p' ++ pi')
    guard $ ppi `elem` posRho
    guard $ ppi' `elem` posRho
    guard $ p `isProperPrefixOf` ppi || p `isProperPrefixOf` ppi'
    Just t <- return $ termAtPos rho ppi
    Just t' <- return $ termAtPos rho ppi'
    return $ t == t'

isProperPrefixOf p1 p2 = isPrefixOf p1 p2 && (not $ p1 == p2)

childTargets :: Term (Transition q t) -> [q]
childTargets t = go (arguments t) where
  go [] = []
  go (child : children) = (target $ root child)  : go children

isRun :: (Eq t, Eq q) => ADC q t -> Term (Transition q t) -> Bool
isRun adc t = let trans = root t in
  childTargets t == fromState trans && (satisfies (fmap symbol t) $ dConstraint trans) && (trans `elem` (transitions adc))

--c' is the set of suffixes of positions ??,????? in atomic constraints of transition rules in ???
c' :: ADC q t -> [Pos]
c' adc = do --TODO c' can be optimized similar to s
    r <- transitions adc
    pi <- (nub $ join $ dConstraint r) >>= \(a,b) -> [a,b]
    suf <- filter (/= []) $ subsequences pi
    guard $ suf `isSuffixOf` pi
    return suf

--s(A)is the number of distinct suffixes of positions ??,????? in an atomic constraint ????=????? in a rule of A
s :: ADC q t -> Int
s adc = length $ nub $ do
    r <- transitions adc
    atom <- (modSym $ nub $ join $ dConstraint r) --distinct atomic constraints
    let pi = fst atom
    let pi' = snd atom
    nub $ (pi : suffixes pi) ++ (pi' : suffixes pi') --for suffixes
    where
      suffixes [] = []
      suffixes (_:xs) = go xs
        where go [] = [] : []
              go f@(_:t) = f: go t

-- n(A???) is the maximum number of atomic constraints in a rule of A???
n :: ADC q t -> Double
n adc = fromIntegral $ maximum $ do
    r <- transitions adc
    return $ length $ join $ dConstraint r
--d(A???) is the maximum length of |??| or |?????| in an atomic constraint ????=????? in a rule of A???
d :: ADC q t -> Int
d adc = maximum $ 0 : do
    r <- transitions adc
    pi <- (nub $ join $ dConstraint r) >>= \(a,b) -> [a,b]
    return $ length pi

h :: ADC q t -> Integer
h adc = div (371828182845 * (toInteger $ length $ states adc) *
           (2^(toInteger $ c adc)) * (fac $ toInteger $ c adc) * (1 + (toInteger $ pi adc))) 100000000000

fac i = product [1..i]

newBfin :: Eq t => ADC q t -> Integer
newBfin adc =
  max
  ((floor beta) * (k) + (floor  gamma))
  ((floor sizeQ) * (toInteger $ length $ nub $ map symbol $ transitions adc))
  where
    sizeQ :: Double
    sizeQ = fromIntegral $ (toInteger $ length $ states adc) * (h adc)
    euler :: Double
    --euler = 2.71828182845
    euler = sum $ map (\i -> 1 / (fromIntegral $ fac i)) [1 .. s adc]
    delta = let s' = s adc in sizeQ * 2^s' * (fromIntegral $ fac s')
    beta = (fromIntegral $ 1 + d adc) * (n adc) * (1.0 + euler * delta)
    gamma = let d' = fromIntegral $ d adc in let n' = n adc in (1 + 2 * d' * n' * euler) * (d' + 1) * n' * (delta)
    k = ceiling $ (beta + sqrt (beta^2 + (4 * gamma))) / 2

newBempty :: Eq t => ADC q t -> Integer
newBempty adc =
  max
  ((floor beta) * (k) + (floor gamma))
  ((floor $ sizeQ) * (toInteger $ length $ nub $ map symbol $ transitions adc))
  where
    sizeQ :: Double
    sizeQ = fromIntegral $ length $ states adc
    euler :: Double
    --euler = 2.71828182845
    euler = sum $ map (\i -> 1 / (fromIntegral $ fac i)) [1 .. s adc]
    delta = let s' = s adc in sizeQ * 2^s' * (fromIntegral $ fac s')
    beta = (fromIntegral $ 1 + d adc) * (n adc) * (1.0 + euler * (delta))
    gamma = let d' = fromIntegral $ d adc in let n' = n adc in (1 + 2 * d' * n' * euler) * (d' + 1) * n' * (delta)
    k = ceiling $ (beta + sqrt (beta^2 + (4 * gamma))) / 2

checkEmptiness :: (Ord q, Ord t) => Integer -> Integer -> ADC q t -> Bool
checkEmptiness h' b !adc = not $ fix (e adc) 0 Map.empty Set.empty where
  c'' = c' adc
  d' = d adc
  f ::  (Ord q, Ord t) => Integer -> ADC q t -> Map.Map q (Set.Set (OrdTerm (Transition q t)))
             -> (Bool, Map.Map q (Set.Set (OrdTerm (Transition q t))), Set.Set (Term (Transition q t)))
             -> Transition q t
             -> (Bool, Map.Map q (Set.Set (OrdTerm (Transition q t))), Set.Set (Term (Transition q t)))
  f i adc' eStar (stop, es, seen) r = foldl g (stop, es, seen) $ do --f is inner for loop (for all rho and phi_i in E*)
    let dom = fromState r
    let m = length $ dom
    rhos <- sequence $ do
          qI <- dom
          Just rhoIs <- return $ Map.lookup qI eStar
          return $ map getTerm $ Set.toList rhoIs
    guard $ length rhos == m
    let rho = treeToTerm r rhos --for each rule build all terms over delta
    guard $ satisfies rho $ dConstraint r --But we still need to check, whether the constraints are satisfied.
    guard $ Set.notMember rho seen --and test, whether we have analysed rho before
    let vs = do
          p <- (pos rho)
          guard $ not $ p `elem` c''
          guard $ (length p) <= (d' + 1)
          Just s <- return $ symbolAtPos rho p --s is a transition, because rho is a term over delta
          Just rhos' <- return $ Map.lookup (target s) eStar
          Just rhoP <- return $ termAtPos rho p
          let descRhos = map getTerm $ Set.toDescList rhos'
          Just smallerRuns <- return $ (findIndex (\x -> rhoP >>> x) descRhos >>= \i -> return $ drop i descRhos) -- TODO: this can be done with a logarithmic number of comparisons (using Set.findIndex and Set.splitAt)
          guard $ b <= (toInteger $ length smallerRuns)
          return $ not $ checkForSequence rho b p smallerRuns --for all p there exists no sequence
    let trgt = target r
    let stop' = trgt `elem` (final adc') && i >= h'
    if and vs
      then --only add terms to eStar, where no sequence exists
      return (stop', Map.insertWith (Set.union) trgt (Set.singleton $ OrdTerm rho) eStar, Set.insert rho seen)
    else
      return (stop', eStar, Set.insert rho seen)
  g (stop, es, seen) (stop', rho, seen') = (stop || stop', Map.unionWith Set.union es rho, Set.union seen seen') --g is outer for loop, for all transitions
  e :: (Ord q, Ord t) => ADC q t -> Integer -> Map.Map q (Set.Set (OrdTerm (Transition q t))) ->
    Set.Set (Term (Transition q t)) ->
    (Bool, Map.Map q (Set.Set (OrdTerm (Transition q t))), Set.Set (Term (Transition q t)))
  e adc' i eStar seen = foldl (f i adc' eStar) (False, Map.empty, seen) $ transitions adc'
  fix f i e r | (\(x, _, _) -> x) (f i e r) = True --if e already contains an accepting run, return true
              | (\(_, x, _) -> x) (f i e r) == e = False --if fixpoint is reached, but no accepting run found, return False
              | otherwise = fix f (i+1) ((\(_, x, _) -> x) $ f i e r) ((\(_, _, y) -> y) $ f i e r)

languageIsEmpty :: (Ord q, Ord t) => ADC q t -> Bool
languageIsEmpty !adc = checkEmptiness 0 (newBempty adc) adc

languageIsFin :: (Ord q, Ord t) => ADC q t -> Bool
languageIsFin !adc = checkEmptiness (h adc) (newBfin adc) adc

intersectionIsFin :: (Ord nt, Newable nt) => TreeGrammar String nt -> RS String IntVar -> Either Bool (Integer, Bool)
intersectionIsFin g r = case eIfIntersectionFin g r of
    Left a -> Left $ languageIsEmpty a
    Right (n, a) -> Right $ (n, languageIsEmpty a)

intersectionIsEmpty :: (Ord nt, Newable nt) => TreeGrammar String nt -> RS String IntVar -> Bool
intersectionIsEmpty g r = languageIsEmpty a where
  a = productADC (constructADC g) (constructNfADC r)

reduce :: Ord q => ADC q t -> ADC q t
reduce adc = ADC (Set.toList $ marked adc ) (qf $ marked adc) (deltaReduced $ marked adc) where
  qf !m = Set.toList $ (Set.fromList $ final adc) `Set.intersection` m
  deltaReduced !m = do
    r <- transitions adc
    let dom = fromState r
    let trgt = target r
    let qs = Set.fromList (trgt : dom)
    guard $ qs `Set.isSubsetOf` m
    return r
  marked :: Ord q => ADC q t -> Set.Set q
  marked adc' = fix (mark adc') Set.empty
  f :: Ord q => Set.Set q -> Transition q t -> Set.Set q
  f marked' r = if (Set.fromList $ fromState r) `Set.isSubsetOf` marked'
    then Set.insert (target r) marked' else marked'
  mark :: Ord q => ADC q t -> Set.Set q -> Set.Set q
  mark adc' marked' = foldl f marked' $ transitions adc'
  fix f s | f s == s = s
          | otherwise = fix f (f s)

ftaDeterminize' :: (Ord q, Eq t) => ADC q t -> ADC [q] t
ftaDeterminize' adc = ADC (nub $ qD) qDf $ nub deltaD where
  qDf = nub $ [f |f <- qD, not $ null $ intersect f $ final adc]
  (qD, deltaD) = fix (g adc) ([], [])
  f :: (Ord q, Eq t) => ADC q t -> ([[q]], [Transition [q] t]) -> t -> ([[q]], [Transition [q] t])
  f adc' (q,d) fn = (insert newQ q, union d newR) where
    newQ = nub $ do
      r <- transitions adc'
      guard $ fn == symbol r
      let test = do
            qi <- fromState r
            return $ not $ null $ filter (\si -> qi `elem` si) q
      guard $ and test
      return $ target r
    newR = nub $ do
      r <- transitions adc'
      guard $ fn == symbol r
      dom <- sequence $ do
            qi <- fromState r
            return $ filter (\si -> qi `elem` si) q
      guard $ (length dom) == (length $ fromState r)
      return $ Transition fn dom newQ $ dConstraint r
  g :: (Ord q, Eq t) => ADC q t -> ([[q]], [Transition [q] t]) -> ([[q]], [Transition [q] t])
  g adc' p = foldl (f adc') p $ nub $ map symbol $ transitions adc'
  fix f p | (snd $ f p) == (snd p) = p
          | otherwise = fix f (f p)

ftaDeterminize :: (Ord q, Eq t) => ADC q t -> ADC Int t
ftaDeterminize = reduce . simplifyStates . ftaDeterminize'

ftaEmptiness ::  Ord q => ADC q t -> Bool
ftaEmptiness = null . final . reduce

ftaInfiniteness :: Ord q => ADC q t -> Bool
ftaInfiniteness adc = (not $ null $ final adc') && (checkLoops $ fix reach $ final adc') where
  adc' = reduce adc
  trans = transitions adc'
  states' = states adc'
  loops = do
    q <- states'
    guard $ q `elem` (loop q)
    return q
  loop q = do
    r <- trans
    guard $ target r == q
    fix reach $ fromState r
  reach' qs = union qs $ nub $ do
    q <- qs
    r <- filter ((q ==) . target) trans
    fromState r
  reach qs =  nub $ qs ++ do
    q <- qs
    r <- filter ((q ==) . target) trans
    fromState r
  fix f x | f x == x = x
          | otherwise = fix f (f x)
  checkLoops xs = or $ do
    x <- xs
    return $ x `elem` (loop x)

ftaFiniteness :: Ord q => ADC q t -> Bool
ftaFiniteness adc = (not $ null $ final adc') && (not $ checkLoops $ fix reach $ final adc') where
  adc' = reduce adc
  trans = transitions adc'
  states' = states adc'
  loop q = do
    r <- trans
    guard $ target r == q
    fix reach $ fromState r
  reach qs =  nub $ qs ++ do
    q <- qs
    r <- filter ((q ==) . target) trans
    fromState r
  fix f x | f x == x = x
          | otherwise = fix f (f x)
  checkLoops xs = or $ do
    x <- xs
    return $ x `elem` (loop x)
