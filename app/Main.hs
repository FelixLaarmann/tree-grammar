module Main where
import Term
import RS
import ADC
import Grammar
import Examples
import CLSoutput

import Control.Unification.IntVar
import Control.Unification.Types
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Control.Monad


main :: IO ()
main = do
  putStrLn "BOOL intersection is empty:"
  print $ ftaEmptiness interBool
  putStrLn "BOOL intersection is finite:"
  print $ ftaFiniteness interBool
  putStrLn "SORT intersection is empty:"
  print $ ftaEmptiness interSort
  putStrLn "SORT intersection is finite:"
  print $ ftaFiniteness interSort
  putStrLn "CLS Labyrinth intersection is empty:"
  print $ ftaEmptiness interCLS
  putStrLn "CLS Labyrinth intersection is finite:"
  print $ ftaFiniteness interCLS


interBool = productADC (constructADC boolGrammar) (constructNfADC boolRS')
interSort = simplifyStates $ reduce $ productADC (constructADC sortGrammar) (constructNfADC sortRS')

labG = labyrinthGrammar 3 4 [(0,0), (1,2), (2,0)] (0,2) (1,0)
labG' = labyrinthGrammar 10 10 [(0,0), (1,2), (2,0), (5,5), (5,6), (8,9)] (1,0) (9,9)

interLab = simplifyStates $ productADC (constructADC labG') (constructNfADC labyrinthRS)

interCLS = simplifyStates $ productADC (constructADC clsGrammar) (constructNfADC $ clsRS)
