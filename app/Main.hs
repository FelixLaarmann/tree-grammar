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
  putStrLn "language of normal forms of boolRS' is finite:"
  putStrLn ""
  print $  languageIsFin $ constructNfADC boolRS
  putStrLn ""
  --putStrLn "Intersection of boolGrammar and boolRS' is finite:"
  --putStrLn ""
  --print $  languageIsFin inter'
  --putStrLn ""
  --print $ intersectionIsEmpty sortGrammar sortRS'
  --print $ accepts inter sortInhabitant
  --print $ length $  fst $ e inter (fst d') (snd d')
  --print $ length $ fst d'
  --mapM_ print $ map (fmap symbol) $ fst d'
  --print $ containsAcceptingRun inter (fst d')
  --print $ sortInhabitant
  --print $ maximum $ map (oldB inter) $ transitions inter
  --print $ maximum $ map (newB inter) $ transitions inter
  --print $ h inter
  --print $ h $ reduce inter

inter = productADC (constructADC sortGrammar) (constructNfADC sortRS)
inter' = productADC (constructADC boolGrammar) (constructNfADC boolRS')
--a = e inter ls Map.empty
--b' = e inter (fst a) (snd a)
--c'' = e inter (fst b') (snd b')
--d' = e inter (fst c'') (snd c'')
--ls :: [Term (Transition (Int, Int) String)]
--ls = []

{-
B := T | F | AND(B,B)

RS :
AND(F,F) -> F
AND(F,T) -> F
AND(T,F) -> F
AND(T,T) -> T
{AND (X,X) -> X}


NF(RS) = {T,F}
-}

