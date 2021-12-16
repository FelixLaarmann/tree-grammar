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
