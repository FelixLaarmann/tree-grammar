{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}


module Examples where
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
import ADC
import Grammar

{-
Example from Lukasz slides (Pres01, slide 21)
x -> 0
y -> 1
-}
{-
f(x,x) -> a
f(g(x,a), g(b,y)) -> c
-}

exampleRS :: RS String IntVar
exampleRS = [(UTerm $ App (UTerm (App (UTerm $ Symbol "f") (UVar $ IntVar 0))) (UVar $ IntVar 0),
              UTerm $ Symbol "a"),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)) (UTerm $ Symbol "a"))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UTerm $ Symbol "b")) (UVar $ IntVar 1)),
              UTerm $ Symbol "c")]


{-
Example for testing
f(x,x) -> a
f(g(x,a), g(b,y)) -> c
h(f(x,y), f(b, g(x,a))) -> d
h(g(a,x), g(x,x)) -> c
-}
testRS :: RS String IntVar
testRS = [(UTerm $ App (UTerm (App (UTerm $ Symbol "f") (UVar $ IntVar 0))) (UVar $ IntVar 0),
              UTerm $ Symbol "a"),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)) (UTerm $ Symbol "a"))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UTerm $ Symbol "b")) (UVar $ IntVar 1)),
              UTerm $ Symbol "c"),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "h") (UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UVar $ IntVar 0)) (UVar $ IntVar 1))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UTerm $ Symbol "b")) (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)) (UTerm $ Symbol "a"))),
              UTerm $ Symbol "d"),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "h") (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UTerm $ Symbol "a")) (UVar $ IntVar 0))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)) (UVar $ IntVar 0)),
              UTerm $ Symbol "c")]

{-
Example for second guard in deltaR'
-}
nextExample :: RS String IntVar
nextExample = [(UTerm $ App (UTerm (App (UTerm $ Symbol "f") (UVar $ IntVar 0))) (UVar $ IntVar 0),
              UTerm $ Symbol "a"),
             (UTerm $ App (UTerm $ App (UTerm $ Symbol "f") (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0))) (UTerm $ App (UTerm $ Symbol "g") (UVar $ IntVar 0)),
              UTerm $ Symbol "b")]

{-
normalized regular tree grammar
-}
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

natListRS :: RS String IntVar
natListRS = [
  --(UTerm $ App (UTerm $ App (UTerm $ Symbol "++") (UTerm $ Symbol "nil")) (UVar $ IntVar 0),
  --UVar $ IntVar 0),
  --(UTerm $ App (UTerm $ App (UTerm $ Symbol "++") (UVar $ IntVar 0)) (UTerm $ Symbol "nil"),
  --UVar $ IntVar 0),
  (UTerm $ App (UTerm $ App (UTerm $ Symbol "mult") (UTerm $ Symbol "0")) (UVar $ IntVar 0),
  UTerm $ Symbol "0"),
  (UTerm $ App (UTerm $ App (UTerm $ Symbol "mult") (UVar $ IntVar 0)) (UTerm $ Symbol "0"),
  UTerm $ Symbol "0")
            ]

t = UTerm $ App (UTerm $ App (UTerm $ Symbol "cons") (UTerm $ App (UTerm $ Symbol "s") (UTerm $ Symbol "0"))) (UTerm $ App (UTerm $ App (UTerm $ Symbol "cons") (UTerm $ Symbol "0")) (UTerm $ Symbol "nil"))

{-
Examples from
"
CLS-SMT: Bringing Together Combinatory Logic
Synthesis and Satisfiability Modulo Theories
"
paper.
-}

{-
sort Example
-}
sortTerminals = ["values", "id", "inv", "sortmap", "min", "default"]

{-
0 := double
1 := double -> double
2 := minimal :&: double
3 := List(double)
4 := SortedList(double)
-}
sortNonTerminals = [0..4]

sortGrammar :: TreeGrammar String Int
sortGrammar = (2, sortNonTerminals, sortTerminals, rules) where
  rules = [
    (4, Terminal "sortmap" [NonTerminal 1, NonTerminal 3]),
    (2, Terminal "id" [NonTerminal 2]),
    (2, Terminal "min" [NonTerminal 0, NonTerminal 4]),
    (0, Terminal "id" [NonTerminal 0]),
    (0, Terminal "default" []),
    (0, Terminal "inv" [NonTerminal 0]),
    (0, Terminal "min" [NonTerminal 0, NonTerminal 4]),
    (1, Terminal "id" [NonTerminal 1]), --here is a a little problem, compared to the paper, because i can not "switch" arity of id in this implementation
    (1, Terminal "inv" [NonTerminal 1]), --same for inv o.O
    (3, Terminal "id" [NonTerminal 3]),
    (3, Terminal "values" [])
          ]

sortRS :: RS String IntVar
sortRS = [
  (
    UTerm $ App (UTerm $ Symbol "id") (UVar $ IntVar 0),
    UVar $ IntVar 0
  ), -- id(x) -> x
  (
    UTerm $ App (UTerm $ App (UTerm $ Symbol "min") (UVar $ IntVar 0)) (UVar $ IntVar 1),
    UTerm $ App (UTerm $ App (UTerm $ Symbol "min") (UTerm $ Symbol "default")) (UVar $ IntVar 1)
  ) -- first argument of min has to be a terminal (there is only one solution, so we hardcode it, because I have no plan how to do it in another way :D)
         ]
