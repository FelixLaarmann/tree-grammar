{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}


module Grammar where
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
We model Trees as following, to enforce non-terminal symbols
to have arity 0.
-}

data T t nt = Terminal !t ![T t nt] | NonTerminal nt deriving (Show, Eq)

{-
A regular tree grammar G = (S,N,F,R) is a tree grammar
such that all non-terminal symbols have arity 0 and
production rules have the form A → β,
with A a non-terminal of N and β a tree of T (F ∪ N ).

A regular tree grammar requires F and N to be disjoint. Therefore
Either t nt is equivalent to F ∪ N.
-}
data TreeGrammar t nt = TreeGrammar
                        { axiom :: !nt
                        , nonTerminals :: ![nt]
                        , terminals :: ![t]
                        , rules :: ![(nt, T t nt)]
                        } deriving (Show, Eq)

class Newable n where
  new :: [n] -> n

instance Newable Int where
  new is = succ (maximum is)

instance Newable String where
  new strings = "new_" ++ (show $ succ $ maximum $ map (sum . map fromEnum) strings)

instance Newable (UTerm (TermV String) IntVar) where
  new qs = UTerm $ SymbolV $ new $ symbols qs where
    symbols (UVar _ :ls) = symbols ls
    symbols (UTerm (SymbolV f):ls) = f : symbols ls
    symbols (UTerm (AppV l r) :ls) = symbols [l] ++ symbols [r] ++ symbols ls
    symbols [] = []

{-
instance Newable a => Newable (Q0 a) where
  new = new . (>>= fromQ) where
    fromQ AcceptOnlyReducible = []
    fromQ (Q x) = x
-}

iterateUntilFix f x = let next = f x in if (x == next) then x else iterateUntilFix f next

transitiveClosure :: (Eq t, Eq nt) => [(nt, T t nt)] -> [(nt, T t nt)]
transitiveClosure r = iterateUntilFix closure r where
  closure r = nub $ r ++ [(a,c) | (a, NonTerminal b) <- r, (b', c) <- r, b == b']

pseudoNormalize :: (Eq t, Eq nt, Newable nt) => TreeGrammar t nt -> TreeGrammar t nt
pseudoNormalize tg = TreeGrammar (axiom tg) n' (terminals tg) r' where
  replace (a, Terminal t args) (rules, nts) = let (args', nts', newRules) = foldr replace' ([], nts, []) args in
    ((a, Terminal t args'):rules ++ newRules, nts')
  replace r (rules, nts) = (r:rules, nts)
  replace' (Terminal t as) (args, nts, newR) = let next = new nts in
    ((NonTerminal next) : args, next : nts, (next, Terminal t as):newR)
  replace' (NonTerminal nt) (args, nts, newR) = (NonTerminal nt : args, nts, newR)
  (r', n') = foldr replace ([], (nonTerminals tg)) (rules tg)

normalize :: (Eq t, Eq nt, Newable nt) => TreeGrammar t nt -> TreeGrammar t nt
normalize tg  = TreeGrammar (axiom tg) (nonTerminals tg') (terminals tg) ((rules tg') >>= replace) where
  tg' = iterateUntilFix pseudoNormalize tg
  r = rules tg
  tc = transitiveClosure r
  alphaRules = filter alphaRule r
  alphaRule (_, NonTerminal alpha) = not $ elem alpha (nonTerminals tg)
  alphaRule _ = True
  replace (a1, NonTerminal _) = [(a1, alpha) | (ai, alpha) <- alphaRules, elem (a1, NonTerminal ai) tc]
  replace r = [r]




