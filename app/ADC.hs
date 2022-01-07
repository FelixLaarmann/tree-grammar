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

{-
A run of an ADC A on a ground term T is a mapping rho :: pos(T) -> transitions(A).
An ADC can be non-deterministic, which can simply be implemented with lists
in the codomain of rho.

A run is called a weak run, if the disequality constraints are not necessarily
satisfied.

A ground term is accepted by an ADC if there is a run on this term such that rho([])
is a transition whose target is a final state.
-}

nonDetWeakRun :: (Eq q, Eq t) => ADC q t -> Term t -> Pos -> [Transition q t]
nonDetWeakRun adc t p
  | elem p (pos t) = do
      Just sp <- return $ t `symbolAtPos` p
      guard $ sp `elem` (map fst $ findSymbols t)
      trans <- filter ((== sp) . symbol) $ transitions adc
      case zip [1..] $ fromState trans of
        [] -> return trans --transitions with arity 0 are valid without restrictions
        ps -> do
          guard $ and $ do
            (i, qi) <- ps --for each state of the domain
            return $ not $ null $ filter ((== qi) . target) $ nonDetWeakRun adc t $ p ++ [i]
            --we have to check, if there is a run mapping its position to a transition with itself as target
          return trans
  | otherwise = []


weakRun :: (Eq q, Eq t) => ADC q t -> Term t -> Pos -> Maybe (Transition q t)
weakRun adc t p = do
  case nonDetWeakRun adc t p of
    [] -> Nothing
    (t:ts) -> return t

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

nonDetRun :: (Eq q, Eq t) => ADC q t -> Term t -> Pos -> [Transition q t]
nonDetRun adc t p
  | elem p (pos t) = do
      ts <- nonDetWeakRun adc t p
      Just tp <- return $ t `termAtPos` p
      guard $ satisfies tp $ dConstraint ts
      return ts
  | otherwise = []

run :: (Eq q, Eq t) => ADC q t -> Term t -> Pos -> Maybe (Transition q t)
run adc t p
  | elem p (pos t) = do
      trans <- weakRun adc t p
      tp <- t `termAtPos` p
      guard $ satisfies tp $ dConstraint trans
      return trans
  | otherwise = Nothing

accepts :: (Eq q, Eq t) => ADC q t -> Term t -> Bool
accepts adc t = isJust $ do
  trans <- run adc t []
  guard $ target trans `elem` final adc
  return True


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
atoms = nub . join . join . (map dConstraint) . transitions

{-
c(ADC) computes the number of all distinct triples (β,π,π′) such that β is a prefix of
π′and π̸=π′ or π′̸=π is an atom occurring in a constraint of transition rules of ADC.
-}
c :: ADC q t -> Int
c adc = length [(beta, pi, pi') | (pi, pi') <- pis, beta <- inits pi', beta `isPrefixOf` pi'] where
  pis = modSym $ atoms adc

{-
pi(ADC) is the maximum length of π in a constraint π̸=π′ or π′̸=π in ADC.
-}
pi :: ADC q t -> Int
pi = maximum . (0:) . (map (\(l,r) -> max (length l) (length r))) . atoms

{-
(q0 r) is the list of all strict subterms of terms in the union of l1 and l2 (modulo renaming of variables)
for a rewriting system r, plus two special states:
- fresh variable x, which will accept all terms
- AcceptOnlyReducible which will accept only reducible terms of r 
-}

data Q0 t v =  AcceptOnlyReducible | Q !(UTerm (TermV t) v) deriving (Show, Eq, Ord)

{-
instance Eq (Q0 String IntVar) where
  AcceptOnlyReducible == AcceptOnlyReducible = True
  Q t == Q t' = runIdentity $ evalIntBindingT $ t === t'
  _ == _ = False

deriving instance Ord (Q0 String IntVar)
-}

q0withoutAOR :: (BindingMonad (TermV t) v m, Fallible (TermV t) v e, MonadTrans em, MonadError e (em m)) =>
                 RS t v -> em m [UTerm (TermV t) v]
q0withoutAOR r = do
  lin <- l1 r
  nlin' <- l2 r
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
f(q_u_1,...,q_u_n)-c−> q_u where q_u_1,...,q_u_n, q_u ∈ Qr and:
-}
  symbols = symbolsOf rs
  l1s = (either (\_ -> []) (\x -> x) $ evalFBM $ l1 rs)
  nArySymbols = nub [(map fst $ filter ((== n) . snd) symbols, n) | (f, n) <- symbols]
  instanceOfSome t ls = filter (\x -> either (\_ -> False) (\x -> x) $ evalFBM $ (x <:= t)) ls
  fromStates n = sequence $ (take n) $ repeat qr
  fromStatesAOR n = sequence . (take n) . repeat $ AcceptOnlyReducible : (map Q qr)
  isQr AcceptOnlyReducible = True
  isQr _ = False
  tops = [Transition s args AcceptOnlyReducible []  |
          (ls, n) <- nArySymbols, s <- ls, args <- fromStatesAOR n, or $ map isQr args] ++
         --if (at least???) one of the q_u_i’s is q_r
         [Transition s (map Q args) AcceptOnlyReducible []  |
          (ls, n) <- nArySymbols, s <- ls, args <- fromStates n,
          not $ null $ instanceOfSome (treeToTermV s args) l1s]
         --or f(u_1,...,u_n) is an instance of some s∈ L1, then q_u=q_r and c=⊤
  q0without = either (\_ -> []) (\x -> x) $ evalFBM $ q0withoutAOR rs
  constraints = do
    (ls, n) <- nArySymbols
    s <- ls
    args <- fromStates n
    case (evalFBM $ mgu $
          instanceOfSome (treeToTermV s args) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return $ Transition s (map Q args) (Q $ u) form where
          form = do
            l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 rs
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
constructNfADC' constructs an automata with disequality constraints (ADC) from a given
rewriting system rs.
This function implements phase 2 of Lukasz algorithm.

constructNfADC' names the state "senseful" for debugging.
-}
constructNfADC' :: RS String IntVar -> ADC (Q0 String IntVar) String
constructNfADC' rs = ADC{
  states = qr,
  final = map Q $ qrWithout,
  transitions = deltaR' rs qrWithout
                             } where
  qrWithout = either (\_ -> []) (\x -> x) $ evalFBM $
    (q0withoutAOR rs >>= nubByTerms . mguSubsets')
  qr = either (\_ -> []) (\x -> x) $ evalFBM $
    (q0withoutAOR rs >>= nubByTerms . mguSubsets' >>=
     \q0wQr -> return $ AcceptOnlyReducible : (map Q q0wQr))

{-
constructNfADC constructs an automata with disequality constraints (ADC) from a given
rewriting system rs.
This function implements phase 2 of Lukasz algorithm.

constructNfADC uses Int as states for better algorithmic behaviour.
-}
constructNfADC :: RS String IntVar -> ADC (Q0 String IntVar) String
constructNfADC rs = ADC{
  states = qr,
  final = map Q $ qrWithout,
  transitions = deltaR' rs qrWithout
                             } where
  qrWithout = either (\_ -> []) (\x -> x) $ evalFBM $
    (q0withoutAOR rs >>= nubByTerms . mguSubsets')
  qr = either (\_ -> []) (\x -> x) $ evalFBM $
    (q0withoutAOR rs >>= nubByTerms . mguSubsets' >>=
     \q0wQr -> return $ AcceptOnlyReducible : (map Q q0wQr))

{-
constructADC constructs an automata with disequality constraints (ADC)
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
heightADC n ts = ADC (-1 : [0..n]) [n] trans where
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
Automaton eIfIntersectionFin = A x A_n whose  language  is  empty  iff L(G)∩NF(R) is finite, where A = A_G (phase 1) x A_R (phase 2)
Choose n \in Nat to be
n = (e+1) x |G| x 2^(|R|^3 +|R| + 2 ) x (|R|^3)! x |R|
where e = 2,718... is Euler's Number.

For debugging and because its interesting we return the computed n's for each transition in the first
projection
-}

eIfIntersectionFin :: (Eq nt, Newable nt) => TreeGrammar String nt -> RS String IntVar ->
  Either (ADC (nt, (Q0 String IntVar)) String) (Integer, ADC ((nt, (Q0 String IntVar)), Integer) String)
eIfIntersectionFin g r = if n == 0 then Left a else Right (n, productADC a (heightADC n f)) where
  a = productADC (constructADC g) (constructNfADC r)
  f = intersectSymbols r g
  --rs = sizeR r
  fac i = product [1..i] --http://www.willamette.edu/~fruehr/haskell/evolution.html
  n = div (371828182845 * (toInteger $ length $ states a) *
           (2^(toInteger $ c a)) * (fac $ toInteger $ c a) * (toInteger $ pi a)) 100000000000
  --n = div (371828182845 * (sizeG g) * (2^(rs^3 + rs + 2)) * (fac $ rs^3) * rs) 100000000000

--lists and MultiSets do not implement this for Ord
multiSetExtension :: Ord a => (a -> a -> Bool) ->  MultiSet.MultiSet a -> MultiSet.MultiSet a -> Bool
multiSetExtension ord m n = or $ do
  x' <- filter (/= []) $ subsequences $ MultiSet.elems m
  let x = MultiSet.fromList x'
  let y = MultiSet.difference n (MultiSet.difference m x)
  x'' <- x'
  return $ MultiSet.fold (\a b -> b && ord x'' a) True y

(>>>) :: (Ord t) => Term t -> Term t -> Bool
(>>>) rho1 rho2 = lexProd (i rho1) (i rho2) where
  i rho = (depth rho, MultiSet.fromList $ strictSubTerms rho, rho)
  lexProd (d, m, r) (d', m', r') | d == d' = if (m == m') then lpo r r' else multiSetExtension (>>>) m m'
                                 | otherwise = d > d'

childTargets :: Term (Transition q t) -> [q]
childTargets t = go (arguments t) where
  go [] = []
  go (child : children) = (target $ root child)  : go children

isRun :: (Eq t, Eq q) => ADC q t -> Term (Transition q t) -> Bool
isRun adc t = let trans = root t in
  childTargets t == fromState trans && (satisfies (mapTerm symbol t) $ dConstraint trans) && (trans `elem` (transitions adc))

{-
languageIsEmpty has to be called like this
languageIsEmpty = languageIsEmpty' []
because otherwise the type checker complains about the type variable v to be ambiguous :(

For debugging and because its interesting we return the computed b's for each transition in the first
projection
-}
languageIsEmpty' :: (Ord q, Ord t) => [Term (Transition q t)] -> ADC q t -> ([Integer], Bool)
languageIsEmpty' ls adc = (map b $ transitions adc, not $ containsAcceptingRun adc $ fix (e adc) ls Map.empty) where
  nAryProd n = sequence . (take n) . repeat
  c = do
    r <- transitions adc
    pi <- (nub $ join $ dConstraint r) >>= \(a,b) -> [a,b]
    suf <- filter (/= []) $ subsequences pi
    guard $ suf `isSuffixOf` pi
    return suf
  n = fromIntegral $ length $ do -- n(A′) is the number of distinct atomic constraints in the rules of A′
    r <- transitions adc
    (nub $ join $ dConstraint r)
  --d(A′) is the maximum length of |π| or |π′| in an atomic constraint π̸=π′ in a (!!!) rule of A′
  d r = maximum $ 0 : do 
    --r <- transitions adc
    pi <- (nub $ join $ dConstraint r) >>= \(a,b) -> [a,b]
    return $ length pi
  --alpha :: Double
  --alpha = 4 * 2.71828182845 + 2
  gamma = 331.4348136746072 --2 * alpha^2 
  --beta = (log 2 + 1) / (log 2)
  delta = 11.770780163555855 --4 * beta + 2 
  b r = let sizeQ = toInteger $ length $ states adc in
    let d' = fromIntegral $ d r in
      if d' == 0
      then
        max
        (floor $  gamma * (fromIntegral $ sizeQ^2))
        (sizeQ * (toInteger $ length $ nub $ map symbol $ transitions adc))
      else
        max
        (floor $  gamma * (fromIntegral $ sizeQ^2) * (2^(round $ delta * d' * n * (log $ 2 * d' * n))))
        (sizeQ * (toInteger $ length $ nub $ map symbol $ transitions adc))
  --checkDescending t [] = True
  --checkDescending t (t' : ts) = t >>> t' && checkDescending t' ts
  checkForSequence 1 r' es = [[r', e] | e <- es, r' >>> e]
  checkForSequence b' r' es | (fromInteger b') > length es = [] 
                            | otherwise = do
                                 e <- es
                                 guard $ r' >>> e
                                 map (r':) $ checkForSequence (b' - 1) e es
  --isRun :: (Ord q, Ord t, Eq v) => ADC q t -> UTerm (Term (Transition q t)) v -> Bool
  --isRun adc' rho = isJust $ run adc' (mapTerm symbol rho) []
  f ::  (Ord q, Ord t) => ADC q t -> [Term (Transition q t)]
             -> ([Term (Transition q t)], Map.Map (Term (Transition q t)) Bool)
             -> Transition q t
             -> ([Term (Transition q t)],
                 Map.Map (Term (Transition q t)) Bool)
  f adc' eStar (es, rhoMap) r = foldl g (es, rhoMap) $ do --f is inner for loop (for all rho and phi_i in E*)
    let m = length $ fromState r
    rhos <- nAryProd m eStar
    guard $ length rhos == m
    let rho = treeToTerm r rhos --for each rule build all terms over delta
    guard $ isRun adc' rho  
    guard $ (Map.lookup rho rhoMap) /= Just True --and test, whether we have analysed rho before
    let vs = do
          p <- (pos rho)
          guard $ not $ p `elem` c
          guard $ (length p) <= ((d r) + 1)
          Just s <- return $ symbolAtPos rho p
          let rhos' = filter (\t -> case symbolAtPos t [] of {Nothing -> False; Just s' -> target s' == target s}) eStar
          Just rhoP <- return $ termAtPos rho p
          --rho' <- nAryProd (fromInteger $ b r) rhos'
          --let rho' = case msort rhos' of {Nothing -> []; Just x -> x}
          let seqs = checkForSequence (b r) rhoP rhos' --rhos' should be nubbed by construction.
          guard $ not $ null seqs
          let rho' = head seqs
          --guard $ checkDescending rhoP rho'
          Just eqCheck <- return $ sequence $ map (\t -> substituteAtPos rho t p) rho'
          return $ and $ map (\t -> not $ containsCloseEq t p) eqCheck
    guard $ and vs
    return (rho, Map.insert rho True rhoMap)
  g (es, rhoMap) (rho, rhoMap') = (union es [rho], Map.union rhoMap rhoMap') --g is outer for loop, for all transitions
  e :: (Ord q, Ord t) => ADC q t -> [Term (Transition q t)] ->
    Map.Map (Term (Transition q t)) Bool ->
    ([Term (Transition q t)], Map.Map (Term (Transition q t)) Bool)
  e adc' eStar rhoMap = foldl (f adc' eStar) ([], Map.empty) $ transitions adc'
  fix f e r | fst (f e r) == e = e
            | containsAcceptingRun adc e = e --we should be able to stop before the fixpoint, if we add an accepting run to eStar
            | otherwise = fix f (fst $ f e r) (snd $ f e r)
  containsCloseEq rho p = or $ do
    let posRho = pos rho
    p' <- posRho 
    guard $ p' `isPrefixOf` p --is this the right implementation for p' <= p????
    Just s <- return $ symbolAtPos rho p'
    let pis = (nub $ join $ dConstraint s) >>= \(a,b) -> [a,b]
    pi <- pis
    pi' <- pis
    guard $ (p' ++ pi) `elem` posRho
    guard $ (p' ++ pi') `elem` posRho
    guard $ p' `isProperPrefixOf` pi || p' `isProperPrefixOf` pi' --is this the right implementation for p' < p????
    Just t <- return $ termAtPos rho (p' ++ pi)
    Just t' <- return $ termAtPos rho (p' ++ pi')
    return $ t == t'
  isProperPrefixOf p1 p2 = isPrefixOf p1 p2 && (not $ p1 == p2)
  containsAcceptingRun :: (Ord q, Ord t) => ADC q t -> [Term (Transition q t)] -> Bool
  containsAcceptingRun adc' eStar = or $ map ((accepts adc') . (mapTerm symbol)) eStar

intersectionIsFin :: (Ord nt, Newable nt) => TreeGrammar String nt -> RS String IntVar -> Bool
intersectionIsFin g r = case eIfIntersectionFin g r of
    Left a -> snd $ languageIsEmpty' ls' a
    Right (n, a) -> snd $ languageIsEmpty' ls a
  where
  ls :: (Ord nt, Newable nt) => [Term (Transition ((nt, (Q0 String IntVar)), Integer) String)]
  ls = []
  ls' :: (Ord nt, Newable nt) => [Term (Transition (nt, (Q0 String IntVar)) String)]
  ls' = []

intersectionIsEmpty :: (Ord nt, Newable nt) => TreeGrammar String nt -> RS String IntVar -> Bool
intersectionIsEmpty g r = snd $ languageIsEmpty' ls a where
  a = productADC (constructADC g) (constructNfADC r)
  ls :: (Ord nt, Newable nt) => [Term (Transition ((nt, (Q0 String IntVar))) String)]
  ls = []



{-
Everything below is for Debugging...
There is a problem with deltaR', because nullaryConstraints and binaryConstraints are empty for exampleRS

Usually exampleRS is part of app/Examples.hs
-}

{-
exampleRS :: RS String IntVar
exampleRS = [(UTerm $ App (UTerm (App (UTerm $ Symbol "cons") (UVar $ IntVar 0))) (UVar $ IntVar 0),
              UTerm $ Symbol "a"),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "cons") (UTerm $ App (UTerm $ App (UTerm $ Symbol "cons") (UVar $ IntVar 0)) (UTerm $ Symbol "a"))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "cons") (UTerm $ Symbol "b")) (UVar $ IntVar 1)),
              UTerm $ Symbol "c")--,
              --((UTerm $ App (UTerm $ App (UTerm $ App (UTerm $ Symbol "test") (UTerm $ Symbol "b")) (UVar $ IntVar 1)) (UTerm $ Symbol "a")),
              --UTerm $ Symbol "c")
            ]

natListGrammar :: TreeGrammar String Int
natListGrammar = (0, [0,1], ["nil", "cons", "0", "s"], rules) where
  rules = [
    (0, Terminal "nil" []),
    (0, Terminal "cons" [NonTerminal 1, NonTerminal 0]),
    (0, Terminal "++" [NonTerminal 0, NonTerminal 0]),
    (1, Terminal "0" []),
    (1, Terminal "s" [NonTerminal 1]),
    (1, Terminal "mult" [NonTerminal 1, NonTerminal 1])
          ]

{-
This is a term, that should not be accepted by natListGrammar.
-}
testTerm :: UTerm (Term String) IntVar
testTerm = UTerm $ App (UTerm $ App (UTerm $ App (UTerm $ Symbol "cons") (UTerm $ Symbol "0")) (UTerm $ App (UTerm $ Symbol "s") (UTerm $ Symbol "0"))) (UTerm $ Symbol "nil")

testTerm' = (UTerm $ App (UTerm $ App (UTerm $ Symbol "cons") (UTerm $ Symbol "0")) (UTerm $ Symbol "nil"))
-}

{-
sort Example
-}

sortTerminals = ["values", "id", "inv", "sortmap", "min", "default", "app"]

{-
0 := double
1 := double -> double
2 := minimal :&: double
3 := List(double)
4 := SortedList(double)
-}

sortNonTerminals = [0..4]

sortGrammar :: TreeGrammar String Int
sortGrammar = TreeGrammar 2 sortNonTerminals sortTerminals rules where
  rules = [
    (4, Terminal "app" [Terminal "app" [Terminal "sortmap" [], NonTerminal 1], NonTerminal 3]),
    (2, Terminal "app" [Terminal "id" [], NonTerminal 2]),
    (2, Terminal "app" [Terminal "app" [Terminal "min" [], NonTerminal 0], NonTerminal 4]),
    (0, Terminal "app" [Terminal "id" [], NonTerminal 0]),
    (0, Terminal "default" []),
    (0, Terminal "app" [Terminal "inv" [], NonTerminal 0]),
    (0, Terminal "app" [Terminal "app" [Terminal "min" [], NonTerminal 0], NonTerminal 4]),
    (1, Terminal "id" []), 
    (1, Terminal "inv" []), 
    (3, Terminal "app" [Terminal "id" [], NonTerminal 3]),
    (3, Terminal "values" [])
          ]


sortRS :: RS String IntVar
sortRS = RS
  [("values", 0), ("id", 0), ("inv", 0), ("sortmap", 0), ("min", 0), ("default", 0), ("app", 2)]
  [
  (
    app (UTerm $ SymbolV "id") (UVar $ IntVar 0),
    UVar $ IntVar 0
  ), -- id(x) -> x
  (
    app (UTerm $ SymbolV "inv") (app (UTerm $ SymbolV "inv") (UVar $ IntVar 0)),
    UVar $ IntVar 0
  ), -- inv(inv(x)) -> x
  (
    app
    (app (UTerm $ SymbolV "sortmap") (UVar $ IntVar 0))
    (app (app (UTerm $ SymbolV "sortmap") (UVar $ IntVar 1)) (UVar $ IntVar 2)),
    app (app (UTerm $ SymbolV "sortmap") (UVar $ IntVar 0)) (UVar $ IntVar 2)
  ) -- sortmap(x, sortmap (y, z)) -> sortmap(x,z)
  --(
  --  app (app (UTerm $ SymbolV "min") (UTerm $ SymbolV "values")) (UTerm $ SymbolV "default"),
  --  UTerm $ SymbolV "default"
  --) -- min(values, default) -> default !!!we have to give a signature to constructNfADC to cover the case, that the RS just use a subsignature of the grammar!!!
  -- min(min(x,y),y) -> min(x,y)
  ]

-- app (app (min) (default)) (app (app (sortmap) (id)) (values))

app l r = UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "app") (l)) (r)
app' l r =  App (App (Symbol "app") (l)) (r)
sortInhabitant :: Term String
sortInhabitant = app' (app' (Symbol "min") (Symbol "default")) (app' (app' (Symbol "sortmap") (Symbol "id")) (Symbol "values"))
acc = accepts $ constructADC sortGrammar
emptyTest = snd $ languageIsEmpty' ls $ constructADC sortGrammar where
  ls :: [Term (Transition Int String)]
  ls = []
test = acc sortInhabitant == not emptyTest

nAryProd n = sequence . (take n) . repeat
c' adc = do
    r <- transitions adc
    pi <- (nub $ join $ dConstraint r) >>= \(a,b) -> [a,b]
    suf <- filter (/= []) $ subsequences pi
    guard $ suf `isSuffixOf` pi
    return suf
n adc = fromIntegral $ length $ do -- n(A′) is the number of distinct atomic constraints in the rules of A′
    r <- transitions adc
    (nub $ join $ dConstraint r)
  --d(A′) is the maximum length of |π| or |π′| in an atomic constraint π̸=π′ in a (!!!) rule of A′
d r = maximum $ 0 : do 
    --r <- transitions adc
    pi <- (nub $ join $ dConstraint r) >>= \(a,b) -> [a,b]
    return $ length pi
  --alpha :: Double
  --alpha = 4 * 2.71828182845 + 2
gamma :: Double
gamma = 331.4348136746072 --2 * alpha^2 
  --beta = (log 2 + 1) / (log 2)
delta :: Double
delta = 11.770780163555855 --4 * beta + 2 
b r adc = let sizeQ = toInteger $ length $ states adc in
    let d' = fromIntegral $ d r in
      if d' == 0
      then
        max
        (floor $  gamma * (fromIntegral $ sizeQ^2))
        (sizeQ * (toInteger $ length $ nub $ map symbol $ transitions adc))
      else
        max
        (floor $  gamma * (fromIntegral $ sizeQ^2) * (2^(round $ delta * d' * (n adc) * (log $ 2 * d' * (n adc)))))
        (sizeQ * (toInteger $ length $ nub $ map symbol $ transitions adc))
  --checkDescending t [] = True
  --checkDescending t (t' : ts) = t >>> t' && checkDescending t' ts
checkForSequence 1 r' es = [[r', e] | e <- es, r' >>> e]
checkForSequence b' r' es | (fromInteger b') > length es = [] 
                            | otherwise = do
                                 e <- es
                                 guard $ r' >>> e
                                 map (r':) $ checkForSequence (b' - 1) e es
--isRun :: (Ord q, Ord t, Eq v) => ADC q t -> UTerm (Term (Transition q t)) v -> Bool
--isRun adc' rho = isJust $ run adc' (mapTerm symbol rho) []
f ::  (Ord q, Ord t) => ADC q t -> [Term (Transition q t)]
             -> ([Term (Transition q t)], Map.Map (Term (Transition q t)) Bool)
             -> Transition q t
             -> (ADC q t -> [Pos])
             -> ([Term (Transition q t)],
                 Map.Map (Term (Transition q t)) Bool)
f adc' eStar (es, rhoMap) r c' = foldl g (es, rhoMap) $ do --f is inner for loop (for all rho and phi_i in E*)
    let m = length $ fromState r
    rhos <- nAryProd m eStar
    guard $ length rhos == m
    let rho = treeToTerm r rhos --for each rule build all terms over delta
    guard $ isRun adc' rho  
    guard $ (Map.lookup rho rhoMap) /= Just True --and test, whether we have analysed rho before
    let vs = do
          p <- (pos rho)
          guard $ not $ p `elem` (c' adc')
          guard $ (length p) <= ((d r) + 1)
          Just s <- return $ symbolAtPos rho p
          let rhos' = filter (\t -> case symbolAtPos t [] of {Nothing -> False; Just s' -> target s' == target s}) eStar
          Just rhoP <- return $ termAtPos rho p
          --rho' <- nAryProd (fromInteger $ b r) rhos'
          --let rho' = case msort rhos' of {Nothing -> []; Just x -> x}
          let seqs = checkForSequence (b r adc') rhoP rhos' --rhos' should be nubbed by construction.
          guard $ not $ null seqs
          let rho' = head seqs
          --guard $ checkDescending rhoP rho'
          Just eqCheck <- return $ sequence $ map (\t -> substituteAtPos rho t p) rho'
          return $ and $ map (\t -> not $ containsCloseEq t p) eqCheck
    guard $ and vs
    return (rho, Map.insert rho True rhoMap)
g (es, rhoMap) (rho, rhoMap') = (union es [rho], Map.union rhoMap rhoMap') --g is outer for loop, for all transitions
e :: (Ord q, Ord t) => ADC q t -> [Term (Transition q t)] ->
    Map.Map (Term (Transition q t)) Bool ->
    ([Term (Transition q t)], Map.Map (Term (Transition q t)) Bool)
e adc' eStar rhoMap = foldl (\ a b -> f adc' eStar a b c') ([], Map.empty) $ transitions adc'
fix' f e r adc  | fst (f e r) == e = e
--           | containsAcceptingRun adc e = e
           | otherwise = fix' f (fst $ f e r) (snd $ f e r) adc
containsCloseEq rho p = or $ do
    let posRho = pos rho
    p' <- posRho
    guard $ p' `isPrefixOf` p --is this the right implementation for p' <= p????
    Just s <- return $ symbolAtPos rho p'
    let pis = (nub $ join $ dConstraint s) >>= \(a,b) -> [a,b]
    pi <- pis
    pi' <- pis
    guard $ (p' ++ pi) `elem` posRho
    guard $ (p' ++ pi') `elem` posRho
    guard $ p' `isProperPrefixOf` pi || p' `isProperPrefixOf` pi' --is this the right implementation for p' < p????
    Just t <- return $ termAtPos rho (p' ++ pi)
    Just t' <- return $ termAtPos rho (p' ++ pi')
    return $ t == t'
isProperPrefixOf p1 p2 = isPrefixOf p1 p2 && (not $ p1 == p2)
containsAcceptingRun :: (Ord q, Ord t) => ADC q t -> [Term (Transition q t)] -> Bool
containsAcceptingRun adc' eStar = or $ map ((accepts adc') . (mapTerm symbol)) eStar




