module Main where
import Term
import RS
import ADC
import Grammar
import Examples
import CLSoutput

import Data.List
import Control.Monad

{-
boolGrammar corresponds to grammar G_B from Example 1 in section 8.1 of the paper.
boolRS' corresponds to the linear version of the rewriting system RS^lin_B from Example 1.
boolRS corresponds to the non-linear version.
-}
interBool = reduce $ simplifyStates $ productADC (constructADC boolGrammar) (constructNfADC boolRS')

{-
sortGrammar corresponds to grammar G_sort from Example 2 in section 8.2 of the paper.
sortRS' corresponds to the linear version of the rewriting system RS^lin_sort from Example 2.
sortRS  corresponds to the non-linear version.
-}
interSort = reduce $ simplifyStates $ productADC (constructADC sortGrammar) (constructNfADC sortRS')

{-
clsGrammar is an adopted CLS-generated grammar for a 30x30 labyrinth.
cslRS corrresponds to RS_CLS from Example 3 in section 8.3 of the paper.
-}
interCLS = reduce $ simplifyStates $ productADC (constructADC clsGrammar) (constructNfADC $ clsRS)

main :: IO ()
main = do
  {-
  ####
  Example 1
  ####
  -}
  --prettyPrintADC interBool
  --putStrLn ""
  putStrLn "intersection language of boolGrammar and linear RS is empty:"
  print $ ftaEmptiness interBool
  putStrLn "intersection language of boolGrammar and linear RS is finite:"
  print $ ftaFiniteness interBool
  {-
  --be careful, the following non-linear version will need more time, than anyone of us has ;P
  putStrLn "intersection language of boolGrammar and non-linear RS is empty:"
  print $ intersectionIsEmpty boolGrammar boolRS'
  putStrLn "intersection language of boolGrammar and non-linear RS is finite:"
  print $ intersectionIsFin boolGrammar boolRS'
  -}

  {-
  ####
  Example 2
  ####
  -}
  --prettyPrintADC interSort
  --putStrLn ""
  putStrLn "intersection language of sortGrammar and linear RS is empty:"
  print $ ftaEmptiness interSort
  putStrLn "intersection language of sortGrammar and linear RS is finite:"
  print $ ftaFiniteness interSort
  {-
  --non-linear version:
  putStrLn "intersection language of sortGrammar and non-linear RS is empty:"
  print $ intersectionIsEmpty sortGrammar sortRS
  putStrLn "intersection language of boolGrammar and non-linear RS is finite:"
  print $ intersectionIsFin sortGrammar sortRS
  -}
  
  {-
  ####
  Example 3
  ####
  -}
  --prettyPrintADC interCLS
  --putStrLn ""
  putStrLn "intersection language of clsGrammar and clsRS is empty:"
  print $ ftaEmptiness interCLS
  putStrLn "intersection language of clsGrammar and clsRS is finite:"
  print $ ftaFiniteness interCLS
