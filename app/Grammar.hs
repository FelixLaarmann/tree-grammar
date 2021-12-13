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
--import ADC


{-
Tree Grammars as lists of rules.
Each rule is either a combinator or an application.
A rule Combinator "a -> a" "id" can be read as a terminal with name "id" and a
type (nonterminal) "a -> a".
A rule Apply "b" "a -> b" "a" can be read as "you obtain something of sort b from
applying something of type a -> b to something of sort a".

Then the resulting
grammar isG Æ (A,T, {@}]B,R) for rules R Æ {r j r is in Gstable and not exists A s.t. r Æ A 7!?}
and the request type A from ¡ `? : A. There are three options for rules r 2 R. Nonterminals are
types T and used without subtyping. Terminals are combinators B or the apply symbol "@".
Rules always use combinators without arguments and the apply symbol with two arguments.

Jans Ansatz
-}
data Rule t nt = Combinator nt t | Apply nt nt nt deriving (Show, Eq)

type TreeG t nt = (nt, [nt], [t], [Rule t nt])


{-
Ansatz mehr nach Tata etc.

A regular tree grammar G = (S,N,F,R) is a tree grammar
such that all non-terminal symbols have arity 0 and
production rules have the form A → β,
with A a non-terminal of N and β a tree of T (F ∪ N ).

A regular tree grammar requires F and N to be disjoint. Therefore
Either t nt is equivalent to F ∪ N.
-}

data T' a = Tree a [T' a]

type TreeGrammar' t nt = (nt, [nt], [t], [(nt, T' (Either t nt))])

{-
We could model Trees as following, to enforce non-terminal symbols
to have arity 0.
-}

data T t nt = Terminal t [T t nt] | NonTerminal nt deriving (Show, Eq)

type TreeGrammar t nt = (nt, [nt], [t], [(nt, T t nt)])

data TGrammar t nt = TGrammar{ axiom :: nt
                        , nonTerminals :: [nt]
                        , terminals :: [t]
                        , rules :: [(nt, T t nt)]
                        }

class Newable n where
  new :: [n] -> n

instance Newable Int where
  new is = succ (maximum is)

instance Newable String where
  new strings = "new_" ++ (show $ succ $ maximum $ map (sum . map fromEnum) strings)

instance Newable (UTerm (Term String) IntVar) where
  new qs = UTerm $ Symbol $ new $ symbols qs where
    symbols (UVar _ :ls) = symbols ls
    symbols (UTerm (Symbol f):ls) = f : symbols ls
    symbols (UTerm (App l r) :ls) = symbols [l] ++ symbols [r] ++ symbols ls
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
pseudoNormalize (s, n, f, r) = (s, n', f, r') where
  replace (a, Terminal t args) (rules, nts) = let (args', nts', newRules) = foldr replace' ([], nts, []) args in
    ((a, Terminal t args'):rules ++ newRules, nts')
  replace r (rules, nts) = (r:rules, nts)
  replace' (Terminal t as) (args, nts, newR) = let next = new nts in
    ((NonTerminal next) : args, next : nts, (next, Terminal t as):newR)
  replace' (NonTerminal nt) (args, nts, newR) = (NonTerminal nt : args, nts, newR)
  (r', n') = foldr replace ([], n) r

normalize :: (Eq t, Eq nt, Newable nt) => TreeGrammar t nt -> TreeGrammar t nt
normalize (s, n, f, r) = (s, n', f, r' >>= replace) where
  (_, n', _, r') = iterateUntilFix pseudoNormalize (s, n, f, r)
  tc = transitiveClosure r
  alphaRules = filter alphaRule r
  alphaRule (_, NonTerminal alpha) = not $ elem alpha n
  alphaRule _ = True
  replace (a1, NonTerminal _) = [(a1, alpha) | (ai, alpha) <- alphaRules, elem (a1, NonTerminal ai) tc]
  replace r = [r]

{-
constructADC :: (Eq t, Eq nt, Newable nt) => TreeGrammar t nt -> ADC nt t
constructADC g = ADC n [s] (map transition r) where
  (s, n, _, r) = normalize g
  transition (a, Terminal f args) = Transition f (from args) a [] --partial function, because g is normalized
  from [] = Nothing
  from (NonTerminal a1 : NonTerminal a2 : qs) = Just (a1, a2) --partial function, because g is normalized
-}
{-
Examples for testing


{-
normalized regular tree grammar
-}
natListGrammar :: TreeGrammar String Int
natListGrammar = (0, [0,1], ["nil", "cons", "0", "s"], rules) where
  rules = [
    (0, Terminal "nil" []),
    (0, Terminal "cons" [NonTerminal 1, NonTerminal 0]),
    (1, Terminal "0" []),
    (1, Terminal "s" [NonTerminal 1])
          ]

{-
regular tree grammar
-}
natListGrammar' :: TreeGrammar String Int
natListGrammar' = (0, [0,1], ["nil", "cons", "0", "s"], rules) where
  rules = [
    (0, Terminal "nil" []),
    (0, Terminal "cons" [Terminal "s" [NonTerminal 1], NonTerminal 0]),
    (1, Terminal "0" []),
    (1, Terminal "s" [NonTerminal 1]),
    (1, NonTerminal 1)
          ]
-}

