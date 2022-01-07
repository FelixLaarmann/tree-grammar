module Main where
import Term
import RS
import ADC
import Grammar
import Examples

import Control.Unification.IntVar
import Control.Unification.Types
import qualified Data.Map as Map


main :: IO ()
main = do
  --prettyPrintADC $ constructNfADC exampleRS
  --print $ intersectionIsEmpty sortGrammar sortRS
  --print $ accepts inter sortInhabitant
  --print $ length $  fst $ e inter (fst d') (snd d')
  print $ length $ fst d'
  --mapM_ print $ map (fmap symbol) $ fst d'
  --print $ containsAcceptingRun inter (fst d')
  --print $ sortInhabitant

inter = productADC (constructADC sortGrammar) (constructNfADC sortRS)
a = e inter ls Map.empty
b' = e inter (fst a) (snd a)
c'' = e inter (fst b') (snd b')
d' = e inter (fst c'') (snd c'')
ls :: [Term (Transition (Int, Int) String)]
ls = []

