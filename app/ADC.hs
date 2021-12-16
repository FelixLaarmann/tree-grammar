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

import Term
import RS
import Grammar

{-
Finite Tree Automata with disequality constraints (ADC) as triples
([states], [final states], [transitions])

For CLS only nullary or binary domains of transitions are possible.
-}

data Transition q t = Transition
  { symbol :: t
  , fromState :: [q]
  , target :: q
  , dConstraint :: [[(Pos, Pos)]]--Bool --better [[(pos, pos)]] because this is a formula (conjunction of disjunctions of disequalities)
  -- Top is []
  } deriving Show

data ADC q t = ADC
  { states :: [q]
  , final :: [q]
  , transitions :: [Transition q t]
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
Falls man das mal braucht...
-}
nAryProd :: Int -> [a] -> [[a]]
nAryProd n = sequence . (take n) . repeat

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
pi = maximum . (map (\(l,r) -> max (length l) (length r))) . atoms

{-
(q0 r) is the list of all strict subterms of terms in the union of l1 and l2 (modulo renaming of variables)
for a rewriting system r, plus two special states:
- fresh variable x, which will accept all terms
- AcceptOnlyReducible which will accept only reducible terms of r 
-}

data Q0 t v =  AcceptOnlyReducible | Q (UTerm (Term t) v) deriving (Show)

q0withoutAOR :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
                 RS t v -> em m [UTerm (Term t) v]
q0withoutAOR r = do
  lin <- l1 r
  nlin' <- l2 r
  let nlin = map snd nlin'
  nubbed <- nubByTerms $ (lin >>= strictSubTerms) ++ (nlin >>= strictSubTerms)
  --let modRenaming = filter noUVar nubbed
  modRenaming <- mapM freshen $ filter noUVar nubbed
  x <- lift freeVar
  return $ (UVar x) : modRenaming where --modulo renaming means that each variable in a set of terms has to be distinct.
    noUVar (UVar _) = False
    noUVar _ = True

q0 :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
      RS t v -> em m ([Q0 t v])
q0 r = do
  q0wQr <- q0withoutAOR r
  return $ AcceptOnlyReducible : (map Q q0wQr)

{-
mgu computes the most general unifier of a list of terms
-}
mgu :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em, MonadError e (em m)) =>
       [UTerm (Term t) v] -> em m (UTerm (Term t) v)
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
mguSubsets :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em,
               MonadError e (em m)) =>
               [UTerm (Term t) v] -> [em m (UTerm (Term t) v)]
mguSubsets ts = map mgu $ filter (not . null) $ subsequences ts


mguSubsets' :: [UTerm (Term String) IntVar] -> [UTerm (Term String) IntVar]
mguSubsets' ts = fromErrorList $ map evalFBM $ either (\_ -> []) (\x -> x) $ evalFBM $
  (return . mguSubsets) ts where
    fromErrorList [] = []
    fromErrorList (Left e : es) = fromErrorList es
    fromErrorList (Right t : es) = t : fromErrorList es

{-
deltaR' computes the transitions, when constructing an adc from a rewriting system rs.
For simplicity deltaR' is abstract over the final states of the adc to construct from rs.

deltaR' :: RS String IntVar -> [UTerm (Term String) IntVar]
  -> [Transition (Q0 String IntVar) String]
deltaR' rs qr = tops ++ nullaryConstraints ++ binaryConstraints where 
  symbols = symbolsOf rs
  l1s = (either (\_ -> []) (\x -> x) $ evalFBM $ l1 rs)
  nullarySymbols = map fst $ filter ((== 0) . snd) symbols
  binarySymbols = map fst $ filter ((== 2) . snd) symbols
  nullaryCandidates = [UTerm $ Symbol s | s <- nullarySymbols]
  candidatesForPair p =
    [UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p) | s <- binarySymbols]
  instanceOfSome t ls = filter (\x -> either (\_ -> False) (\x -> x) $ evalFBM $ (x <:= t)) ls
  fromStates = [(a,b) | a <- qr, b <- qr]
  fromStatesAOR = [(Q a, AcceptOnlyReducible) | a <- qr] ++ [(AcceptOnlyReducible, Q a) | a <- qr]
  tops =
    [Transition s (Just p) AcceptOnlyReducible [] | p <- fromStatesAOR, s <- binarySymbols] ++
    [Transition s (Just (Q $ fst p, Q $ snd p)) AcceptOnlyReducible [] | p <- fromStates, s <- binarySymbols,
     not $ null $ instanceOfSome (UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)) l1s] ++
    [Transition s Nothing AcceptOnlyReducible [] | s <- nullarySymbols,
     not $ null $ instanceOfSome (UTerm $ Symbol s) l1s]
  q0without = either (\_ -> []) (\x -> x) $ evalFBM $ q0withoutAOR rs
  nullaryConstraints = do
    s <- nullarySymbols
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ Symbol s) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return $ Transition s Nothing (Q u) form where
          form = do
            l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 rs
            guard $ isRight $ evalFBM $ unify u $ snd l
            let xs = vars $ fst l
            return $ do
              (x, p1) <- xs
              (x', p2) <- filter (\p -> x == fst p) $ delete (x,p1) xs
              return (p1,p2)
{-
Instead of going through (vars l) and building the needed formula "by going through", one can unify the linearized and prelinearized l (from l2) and check the map for multiple occurences of a variable of the prelinearized terms, build the product, compute the positions and build the formula.

This won't work, because the map is not accessible.
-}
      Left _ -> mzero
  binaryConstraints = do
    p <- fromStates
    s <- binarySymbols
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return $ Transition s (Just (Q $ fst p, Q $ snd p)) (Q $ u) form where
          form = do
            l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 rs
            --l is a pair of the prelinearized and the linearized terms
            guard $ isRight $ evalFBM $ unify u $ snd l --here the linearized one has to be used
            let xs = vars $ fst l --here the prelinearized
            return $ do
              --look up all positions, if there are for example 3 or more positions of x, all pairs p1 /= p2 have to be checked.
              (x, p1) <- xs
              (x', p2) <- filter (\p -> x == fst p) $ delete (x,p1) xs
              return (p1,p2)
      Left _ -> mzero
-}

{-
deltaR' computes the transitions for n-ary symbols.
-}
deltaR' :: RS String IntVar -> [UTerm (Term String) IntVar]
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
          not $ null $ instanceOfSome (treeToTerm s args) l1s]
         --or f(u_1,...,u_n) is an instance of some s∈ L1, then q_u=q_r and c=⊤
  q0without = either (\_ -> []) (\x -> x) $ evalFBM $ q0withoutAOR rs
  constraints = do
    (ls, n) <- nArySymbols
    s <- ls
    args <- fromStates n
    case (evalFBM $ mgu $
          instanceOfSome (treeToTerm s args) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return $ Transition s (map Q args) (Q $ u) form where
          form = do
            l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 rs
            --l is a pair of the prelinearized and the linearized terms
            guard $ isRight $ evalFBM $ unify u $ snd l --here the linearized one has to be used
            let xs = vars $ fst l --here the prelinearized
            return $ do
              --look up all positions, if there are for example 3 or more positions of x, all pairs p1 /= p2 have to be checked.
              (x, p1) <- xs
              (x', p2) <- filter (\p -> x == fst p) $ delete (x,p1) xs
              return (p1,p2)
      Left _ -> mzero

{-
constructNfADC constructs an automata with disequality constraints (ADC) from a given
rewriting system rs.
This function implements phase 2 of Lukasz algorithm.
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
constructADC g = ADC n [s] (map transition r) where
  (s, n, _, r) = normalize g
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

--symbolsOf :: Eq t => RS t v -> [(t, Int)]
terminalsWithArity :: Eq t => TreeGrammar t nt -> [(t, Int)]
terminalsWithArity (_, _, _, rules) = nub $ rules >>= (arity . snd) where
  arity (Terminal t args) = (t, length args) : (args >>= arity)
  arity (NonTerminal _) = []

intersectSymbols :: Eq t => RS t v -> TreeGrammar t nt -> [(t, Int)]
intersectSymbols rs gr = intersect (terminalsWithArity gr) (symbolsOf rs)

heightADC :: Eq t => Integer -> [(t, Int)] -> ADC Integer t
heightADC n ts = ADC (-1 : [0..n]) [n] trans where
  trans = map (\a -> Transition a [] 0 []) nullaryTs ++
    [Transition f args (min (1 + maximum args) n) [] |
     (ls, n') <- nArySymbols, f <- ls, args <- nAryProd n' [0..n]]
  nullaryTs = map fst $ filter ((== 0) . snd) ts
  nAryProd n = sequence . (take n) . repeat
  nArySymbols = nub [(map fst $ filter ((== n') . snd) ts, n') | (f, n') <- ts, n' > 0]

{-
[CJ03] defines the size of a term as the cardinal
|Pos(t)| of its positions set.
-}
sizeT :: UTerm (Term t) v -> Integer
sizeT = toInteger . length . pos

{-
I'm not sure how Lukasz defines the size of a tree grammar, but usually the size
of a grammar is something like the sum of the sizes of all right-hand sides of the production rules.
-}
sizeG :: TreeGrammar t nt -> Integer
sizeG (_, _, _, r) = sum $ map (size . snd) r where
  size (Terminal _ ts) = 1 + (sum $ map size ts)
  size (NonTerminal _) = 0

{-
[CJ03] defines the size of a rewrite system R as the
sum of the sizes of its left members
-}
sizeR :: RS t v -> Integer
sizeR r = sum $ map (sizeT . fst) r

{-
Automaton eIfIntersectionFin = A x A_n whose  language  is  empty  iff L(G)∩NF(R) is finite, where A = A_G (phase 1) x A_R (phase 2)
Choose n \in Nat to be
n = (e+1) x |G| x 2^(|R|^3 +|R| + 2 ) x (|R|^3)! x |R|
where e = 2,718... is Euler's Number.
-}

eIfIntersectionFin :: (Eq nt, Newable nt) => TreeGrammar String nt -> RS String IntVar -> ADC ((nt, (Q0 String IntVar)), Integer) String
eIfIntersectionFin g r = productADC a (heightADC n f) where
  a = productADC (constructADC g) (constructNfADC r)
  f = intersectSymbols r g
  --rs = sizeR r
  fac i = product [1..i] --http://www.willamette.edu/~fruehr/haskell/evolution.html
  n = div (371828182845 * (toInteger $ length $ states a) *
           (2^(toInteger $ c a)) * (fac $ toInteger $ c a) * (toInteger $ pi a)) 100000000000
  --n = div (371828182845 * (sizeG g) * (2^(rs^3 + rs + 2)) * (fac $ rs^3) * rs) 100000000000

{-
Everything below is for Debugging...
There is a problem with deltaR', because nullaryConstraints and binaryConstraints are empty for exampleRS

Usually exampleRS is part of app/Examples.hs
-}


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
q0without = either (\_ -> []) (\x -> x) $ evalFBM $ q0withoutAOR exampleRS
nullarySymbols = map fst $ filter ((== 0) . snd) $ symbolsOf exampleRS
qr = either (\_ -> []) (\x -> x) $ evalFBM $ (q0withoutAOR exampleRS >>= nubByTerms . mguSubsets')
fromStates = [(a,b) | a <- qr, b <- qr]
instanceOfSome t ls = filter (\x -> either (\_ -> False) (\x -> x) $ evalFBM $ (x <:= t)) ls

binarySymbols = map fst $ filter ((== 2) . snd) $ symbolsOf exampleRS



nullaryConstraints = do
    s <- nullarySymbols
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ Symbol s) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return $ Transition s Nothing (Q u) form where
          form = do
            l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 exampleRS
            guard $ isRight $ evalFBM $ unify u $ snd l
            let xs = vars $ fst l
            return $ do
              (x, p1) <- xs
              (y, p2) <- filter (\p -> x == fst p) $ delete (x,p1) xs
              return (p1,p2)
      Left _ -> mzero

{-
Instead of going through (vars l) and building the needed formula "by going through", one can unify the linearized and prelinearized l (from l2) and check the map for multiple occurences of a variable of the prelinearized terms, build the product, compute the positions and build the formula.
-}

binaryConstraints = do
    p <- fromStates
    s <- binarySymbols
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return $ Transition s (Just (Q $ fst p, Q $ snd p)) (Q $ u) form where
          form = do
            l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 exampleRS
            guard $ isRight $ evalFBM $ unify u $ snd l
            let xs = vars $ fst l
            return $ do
              (x, p1) <- xs
              (y, p2) <- filter (\p -> x == fst p) $ delete (x,p1) xs
              return (p1,p2)
      Left _ -> mzero

bspT = UVar $ IntVar 0
bspT' = UTerm $ App (UTerm $ Symbol "f") (UVar $ IntVar 1)
bspT'' = UTerm $ App (UTerm $ Symbol "f") (UTerm $ App  (UTerm $ Symbol "g") (UVar $ IntVar 2))
bspT''' = UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)) (UTerm $ Symbol "a"))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UTerm $ Symbol "b")) (UVar $ IntVar 1))
lBspT = UTerm $ App (UTerm (App (UTerm $ Symbol "f") (UVar $ IntVar 1))) (UVar $ IntVar 2)
nlBspT = UTerm $ App (UTerm (App (UTerm $ Symbol "f") (UVar $ IntVar 0))) (UVar $ IntVar 0)
-}
