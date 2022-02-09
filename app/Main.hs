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
  --prettyPrintADC $ constructNfADC exampleRS
  --putStrLn "language of normal forms of boolRS' intersect boolGrammer is finite:"
  {-
  putStrLn "Values of b (emptiness) for each transition:"
  print $ map (newBempty inter') $ transitions inter'
  putStrLn "Values of b (finiteness) for each transition:"
  print $ map (newBfin inter') $ transitions inter'
  putStrLn "Size of eStar for each iteration:"
  putStrLn ""
  putStrLn "0:"
  print $ length $ (Map.toList $ enumerateLanguage 0 $ inter') >>= (Set.toList . snd)
  putStrLn "1:"
  print $ length $ (Map.toList $ enumerateLanguage 1 $ inter') >>= (Set.toList . snd)
  putStrLn "2:"
  print $ length $ (Map.toList $ enumerateLanguage 2 $ inter') >>= (Set.toList . snd)
  putStrLn "3:"
  print $ length $ (Map.toList $ enumerateLanguage 3 $ inter') >>= (Set.toList . snd)
  putStrLn "4:"
  print $ length $ (Map.toList $ enumerateLanguage 4 $ inter') >>= (Set.toList . snd)
  -}
  --putStrLn "4:"
  --print $ length $ (Map.toList $ enumerateLanguage 4 $ constructNfADC boolRS') >>= (Set.toList . snd)
  --mapM_ print $ Set.toList $ (enumerateLanguage 3 inter) Map.! 3
  --putStrLn ""
  --putStrLn "CLS Labyrinth intersection is empty:"
  --print $ ftaEmptiness interCLS
  --prettyPrintADC $ reduce interCLS
  --putStrLn ""
  --putStrLn "3x4 Labyrinth grammar is finite:"
  --print $ ftaFiniteness interLab
  putStrLn "CLS Labyrinth intersection is finite:"
  print $ ftaFiniteness interCLS
  --print $ ftaInfiniteness (constructADC clsGrammar)
  --print $ enumerateLanguage 5 $ constructADC clsGrammar
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

inter = simplifyStates $ reduce $ productADC (constructADC sortGrammar) (constructNfADC sortRS)
inter' = productADC (constructADC boolGrammar) (constructNfADC boolRS')
inter'' = reduce $ productADC (constructNfADC boolRS) (constructNfADC boolRS) --nice minimization :D

labG = labyrinthGrammar 3 4 [(0,0), (1,2), (2,0)] (0,2) (1,0)
labG' = labyrinthGrammar 10 10 [(0,0), (1,2), (2,0), (5,5), (5,6), (8,9)] (1,0) (9,9)

interLab = simplifyStates $ productADC (constructADC labG') (constructNfADC labyrinthRS)

interCLS = simplifyStates $ productADC (constructADC clsGrammar) (constructNfADC $ clsRS)

{-
For Debugging...
-}
loops adc = do
    q <- states adc
    guard $ q `elem` (loop q adc)
    return q
loop q adc = do
    r <- transitions adc
    guard $ target r == q
    fix (reach adc) (fromState r)
reach adc qs = nub $ qs ++ do
    q <- qs
    r <- filter ((q ==) . target) (transitions adc)
    fromState r
fix f x | f x == x = x
        | otherwise = fix f (f x)


--test = fmap (Set.size . snd) (Map.toList $ enumerateLanguage 5 $ constructNfADC boolRS') -- >>= (Set.toList . snd) --Set.size $ enumerateLanguage 4 $ constructNfADC boolRS'
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

