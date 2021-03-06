# Restricting tree grammars with term rewriting
This is the prototype implementation for "Restricting tree grammars with term rewriting".

## Build and run
Simply clone the github repository and use `cabal build` and `cabal run` to build and run the code from  app/Main.hs

## Description
For testing the algorithms one should use app/Main.hs. The implementation is structured as follows:
- app/ADC.hs implements tree automata with disequality constraints and the corresponding algorithms from the paper.
- app/Term.hs, app/RS.hs and app/Grammar.hs implement the datastructures and necessary functions for terms, term rewriting systems and tree grammars.
- app/Examples.hs implements a collection of use cases. The "bool" and "sort" examples are described in the paper.
- app/CLSoutput.hs contains the output tree grammar of the [labyrinth benchmark](https://github.com/combinators/cls-scala/blob/master/examples/src/main/scala/org/combinators/cls/examples/LabyrinthBenchmark.scala) for the [CLS framework](https://github.com/combinators/cls-scala) and a rewriting system equivalent to the labyrinth examples from app/Examples.hs.
- app/Main.hs contains some example calls.

## Notes and limitation
Checking emptiness and finiteness for tree automata with disequality constraints (ADCs) will only terminate fast if the language of the ADC is not empty or infinite.
Otherwise the run times for these EXPTIME-complete algorithms are infeasible.
If all disequality constraints in an ADC are true (`[]` in this implementation), it is equivalent to a finite tree automaton (FTA) by simply ignoring the disequality constraints.
In this case, one should use `ftaEmptiness` and `ftaFiniteness` instead of `languageIsEmpty` and `languageIsFinite` because checking emptiness and finiteness for FTAs is much faster than for ADCs.
