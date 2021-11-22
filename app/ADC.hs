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

import Term
import RS

{-
Finite Tree Automata with disequality constraints (ADC) as triples
([states], [final states], [transitions])

For CLS only nullary or binary domains of transitions are possible.
-}
data Transition q t = Transition
  { symbol :: t
  , fromState :: Maybe (q, q)
  , target :: q
  , dConstraint :: Bool
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
  nlin <- l2 r
  nubbed <- nubByTerms $ (lin >>= strictSubTerms) ++ (nlin >>= strictSubTerms)
  let modRenaming = filter noUVar nubbed
  x <- lift freeVar
  return $ (UVar x) : modRenaming where
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
mgu (t1:t2:ts) = do {
  u1 <- unify t1 t2;
  u2 <- mgu (t2:ts);
  unify u1 u2
  }

{-
mguSubsets computes the powerset modulo unification from a set/list of terms
with the mgu to represent each subset
-}
mguSubsets :: (BindingMonad (Term t) v m, Fallible (Term t) v e, MonadTrans em,
               MonadError e (em m)) =>
               [UTerm (Term t) v] -> [em m (UTerm (Term t) v)]
mguSubsets ts = map ((>>= applyBindings) . mgu) $ filter (not . null) $ subsequences ts


mguSubsets' :: [UTerm (Term String) IntVar] -> [UTerm (Term String) IntVar]
mguSubsets' ts = fromErrorList $ map evalFBM $ either (\_ -> []) (\x -> x) $ evalFBM $
  (return . mguSubsets) ts where
    fromErrorList [] = []
    fromErrorList (Left e : es) = fromErrorList es
    fromErrorList (Right t : es) = t : fromErrorList es

{-
Laut Jan kann es beim CLS nur null- oder zweistellige Transitionen geben
-}
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
    [Transition s (Just p) AcceptOnlyReducible True | p <- fromStatesAOR, s <- binarySymbols] ++
    [Transition s (Just (Q $ fst p, Q $ snd p)) AcceptOnlyReducible True | p <- fromStates, s <- binarySymbols,
     not $ null $ instanceOfSome (UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)) l1s] ++
    [Transition s Nothing AcceptOnlyReducible True | s <- nullarySymbols,
     not $ null $ instanceOfSome (UTerm $ Symbol s) l1s]
  q0without = either (\_ -> []) (\x -> x) $ evalFBM $ q0withoutAOR rs
  nullaryConstraints = do
    s <- nullarySymbols
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ Symbol s) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 rs
        guard $ isRight $ evalFBM $ unify u l
        let xs = vars l
        (x, p1) <- xs
        case (lookup x $ delete (x,p1) xs) of
          Just p2 -> return $ Transition s Nothing (Q $ u) (p1 /= p2)
          Nothing -> mzero
      Left _ -> mzero
  binaryConstraints = do
    p <- fromStates
    s <- binarySymbols
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        l <- either (\_ -> []) (\x -> x) $ evalFBM $ l2 rs
        guard $ isRight $ evalFBM $ unify u l
        let xs = vars l
        (x, p1) <- xs
        case (lookup x $ delete (x,p1) xs) of
          Just p2 -> return $ Transition s (Just (Q $ fst p, Q $ snd p)) (Q $ u) (p1 /= p2)
          Nothing -> mzero
      Left _ -> mzero

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
      case fromState t1 of
        Just (q11, q12) -> case fromState t2 of
          Just (q21, q22) -> return $
            Transition s (Just ((q11, q21), (q12, q22)))
              (target t1, target t2)
              (dConstraint t1 && dConstraint t2)
          Nothing -> mzero
        Nothing -> do
          guard $ isNothing $ fromState t2
          return $
            Transition s Nothing (target t1, target t2) (dConstraint t1 && dConstraint t2)
                       }

--For Debugging... There is a problem with deltaR', because nullaryConstraints and binaryConstraints are empty for exampleRS
exampleRS :: RS String IntVar
exampleRS = [(UTerm $ App (UTerm (App (UTerm $ Symbol "f") (UVar $ IntVar 0))) (UVar $ IntVar 0),
              UTerm $ Symbol "a"),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)) (UTerm $ Symbol "a"))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UTerm $ Symbol "b")) (UVar $ IntVar 1)),
              UTerm $ Symbol "c")]

q0without = either (\_ -> []) (\x -> x) $ evalFBM $ q0withoutAOR exampleRS
nullarySymbols = map fst $ filter ((== 0) . snd) $ symbolsOf exampleRS
qr = either (\_ -> []) (\x -> x) $ evalFBM $ (q0withoutAOR exampleRS >>= nubByTerms . mguSubsets')
fromStates = [(a,b) | a <- qr, b <- qr]
instanceOfSome t ls = filter (\x -> either (\_ -> False) (\x -> x) $ evalFBM $ (x <:= t)) ls

binarySymbols = map fst $ filter ((== 2) . snd) $ symbolsOf exampleRS

nullaryConstraints = do
    s <- nullarySymbols
    return $ instanceOfSome (UTerm $ Symbol s) q0without
    {-
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ Symbol s) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return u
-}

binaryConstraints = do
    p <- fromStates
    s <- binarySymbols
    return $ ((UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)), instanceOfSome (UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)) q0without)
    {-
    case (evalFBM $ mgu $
          instanceOfSome (UTerm $ App (UTerm $ App (UTerm $ Symbol s) (fst p)) (snd p)) q0without) of
      Right u -> do
        guard (elemByTerms' u qr)
        return u
-}
