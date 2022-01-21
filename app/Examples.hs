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
exampleRS = RS
  [("f", 2), ("g", 2), ("a", 0), ("b", 0), ("c", 0)]
  [(UTerm $ AppV (UTerm (AppV (UTerm $ SymbolV "f") (UVar $ IntVar 0))) (UVar $ IntVar 0),
              UTerm $ SymbolV "a"),
             (UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "f") (UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "g") (UVar $ IntVar 0)) (UTerm $ SymbolV "a"))) (UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "g") (UTerm $ SymbolV "b")) (UVar $ IntVar 1)),
              UTerm $ SymbolV "c")]


{-
regular tree grammar
-}
natListGrammar' :: TreeGrammar String Int
natListGrammar' = TreeGrammar 0 [0,1] ["nil", "cons", "0", "s"] rules where
  rules = [
    (0, Terminal "nil" []),
    (0, Terminal "cons" [Terminal "s" [NonTerminal 1], NonTerminal 0]),
    (1, Terminal "0" []),
    (1, Terminal "s" [NonTerminal 1]),
    (1, NonTerminal 1)
          ]

{-
normalized regular tree grammar
-}
natListGrammar :: TreeGrammar String Int
natListGrammar = TreeGrammar 0 [0,1] ["nil", "cons", "0", "s"] rules where
  rules = [
    (0, Terminal "nil" []),
    (0, Terminal "cons" [NonTerminal 1, NonTerminal 0]),
    (1, Terminal "0" []),
    (1, Terminal "s" [NonTerminal 1])
          ]


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
  ), -- sortmap(x, sortmap (y, z)) -> sortmap(x,z)
  (
    app
    (app (UTerm $ SymbolV "min") ((app (app (UTerm $ SymbolV "min") (UVar $ IntVar 0)) (UVar $ IntVar 1))))
    (UVar $ IntVar 1),
    app (app (UTerm $ SymbolV "min") (UVar $ IntVar 0)) (UVar $ IntVar 1)
  )
  -- min(min(x,y),y) -> min(x,y)
  ]

sortRS' :: RS String IntVar
sortRS' = RS
  [("values", 0), ("id", 0), ("inv", 0), ("sortmap", 0), ("default", 0), ("app", 2)]
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
  )
  ]

-- app (app (min) (default)) (app (app (sortmap) (id)) (values))

app l r = UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "app") (l)) (r)
app' l r =  App (App (Symbol "app") (l)) (r)
sortInhabitant :: Term String
sortInhabitant = app' (app' (Symbol "min") (Symbol "default")) (app' (app' (Symbol "sortmap") (Symbol "id")) (Symbol "values"))

{-
Boolean algebra example
-}

boolTerminals = ["T", "F", "AND"]

boolNonTerminals = [0]

boolGrammar :: TreeGrammar String Int
boolGrammar = TreeGrammar 0 boolNonTerminals boolTerminals rules where
  rules = [
    (0, Terminal "T" []),
    (0, Terminal "F" []),
    (0, Terminal "AND" [NonTerminal 0, NonTerminal 0])
          ]

boolRS :: RS String IntVar
boolRS = RS
  [("T", 0), ("F", 0), ("AND", 2)]
  [
    (
      UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "AND") (UTerm $ SymbolV "F")) (UTerm $ SymbolV "F"),
      UTerm $ SymbolV "F"
    ),
    (
      UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "AND") (UTerm $ SymbolV "F")) (UTerm $ SymbolV "T"),
      UTerm $ SymbolV "F"
    ),
    (
      UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "AND") (UTerm $ SymbolV "T")) (UTerm $ SymbolV "F"),
      UTerm $ SymbolV "F"
    ),
    (
      UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "AND") (UTerm $ SymbolV "T")) (UTerm $ SymbolV "T"),
      UTerm $ SymbolV "T"
    )
  ]

boolRS' :: RS String IntVar
boolRS' = RS
  [("T", 0), ("F", 0), ("AND", 2)]
  [
    (
      UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "AND") (UTerm $ SymbolV "F")) (UVar $ IntVar 0),
      UTerm $ SymbolV "F"
    ),
    (
      UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "AND") (UVar $ IntVar 0)) (UTerm $ SymbolV "F"),
      UTerm $ SymbolV "F"
    ),
    (
      UTerm $ AppV (UTerm $ AppV (UTerm $ SymbolV "AND") (UVar $ IntVar 0)) (UVar $ IntVar 0),
      UVar $ IntVar 0
    )
  ] 
