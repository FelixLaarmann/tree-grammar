module Main where
import Term
import RS
import ADC
import Examples

main :: IO ()
main = prettyPrintADC $ constructNfADC exampleRS

{-
Result of main:

States:

AcceptOnlyReducible
Q (IntVar (-9223372036854775806))
Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a"))
Q (Symbol "a")
Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1))
Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))
Q (Symbol "b")



Final States:

Q (IntVar (-9223372036854775806))
Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a"))
Q (Symbol "a")
Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1))
Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))
Q (Symbol "b")



Transitions:

f(Q (IntVar (-9223372036854775806)),AcceptOnlyReducible) - T -> AcceptOnlyReducible

g(Q (IntVar (-9223372036854775806)),AcceptOnlyReducible) - T -> AcceptOnlyReducible

f(Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a")),AcceptOnlyReducible) - T -> AcceptOnlyReducible

g(Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a")),AcceptOnlyReducible) - T -> AcceptOnlyReducible

f(Q (Symbol "a"),AcceptOnlyReducible) - T -> AcceptOnlyReducible

g(Q (Symbol "a"),AcceptOnlyReducible) - T -> AcceptOnlyReducible

f(Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1)),AcceptOnlyReducible) - T -> AcceptOnlyReducible

g(Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1)),AcceptOnlyReducible) - T -> AcceptOnlyReducible

f(Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),AcceptOnlyReducible) - T -> AcceptOnlyReducible

g(Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),AcceptOnlyReducible) - T -> AcceptOnlyReducible

f(Q (Symbol "b"),AcceptOnlyReducible) - T -> AcceptOnlyReducible

g(Q (Symbol "b"),AcceptOnlyReducible) - T -> AcceptOnlyReducible

f(AcceptOnlyReducible,Q (IntVar (-9223372036854775806))) - T -> AcceptOnlyReducible

g(AcceptOnlyReducible,Q (IntVar (-9223372036854775806))) - T -> AcceptOnlyReducible

f(AcceptOnlyReducible,Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a"))) - T -> AcceptOnlyReducible

g(AcceptOnlyReducible,Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a"))) - T -> AcceptOnlyReducible

f(AcceptOnlyReducible,Q (Symbol "a")) - T -> AcceptOnlyReducible

g(AcceptOnlyReducible,Q (Symbol "a")) - T -> AcceptOnlyReducible

f(AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1))) - T -> AcceptOnlyReducible

g(AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1))) - T -> AcceptOnlyReducible

f(AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))) - T -> AcceptOnlyReducible

g(AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))) - T -> AcceptOnlyReducible

f(AcceptOnlyReducible,Q (Symbol "b")) - T -> AcceptOnlyReducible

g(AcceptOnlyReducible,Q (Symbol "b")) - T -> AcceptOnlyReducible

f(Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1))) - T -> AcceptOnlyReducible

f(Q (App (App (Symbol "g") (IntVar 0)) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))) - T-> AcceptOnlyReducible

f(Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar 1))) - T-> AcceptOnlyReducible

f(Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))) -T -> AcceptOnlyReducible
-}

{-
Result of main after "reparation":

##### States #####

AcceptOnlyReducible
Q (IntVar (-9223372036854775804))
Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))
Q (Symbol "a")
Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))
Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))
Q (Symbol "b")



##### Final States #####

Q (IntVar (-9223372036854775804))
Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))
Q (Symbol "a")
Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))
Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))
Q (Symbol "b")



##### Transitions #####

Transition {symbol = "f", fromState = Just (Q (IntVar (-9223372036854775804)),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (Q (IntVar (-9223372036854775804)),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "a"),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (Q (Symbol "a"),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "b"),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (Q (Symbol "b"),AcceptOnlyReducible), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (AcceptOnlyReducible,Q (IntVar (-9223372036854775804))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (AcceptOnlyReducible,Q (IntVar (-9223372036854775804))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (AcceptOnlyReducible,Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (AcceptOnlyReducible,Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (AcceptOnlyReducible,Q (Symbol "a")), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (AcceptOnlyReducible,Q (Symbol "a")), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = AcceptOnlyReducible, dConstraint = []}
Transition {symbol = "g", fromState = Just (AcceptOnlyReducible,Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (AcceptOnlyReducible,Q (Symbol "b")), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "g", fromState = Just (AcceptOnlyReducible,Q (Symbol "b")), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = AcceptOnlyReducible, dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = AcceptOnlyReducible, dConstraint = []}


------------- New Transitions after "reparation" ----------------------------

Transition {symbol = "a", fromState = Nothing, target = Q (Symbol "a"), dConstraint = []}

Transition {symbol = "b", fromState = Nothing, target = Q (Symbol "b"), dConstraint = []}

Transition {symbol = "c", fromState = Nothing, target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (IntVar (-9223372036854775804)),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (IntVar (-9223372036854775804)),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (IntVar (-9223372036854775804)),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (IntVar (-9223372036854775804)),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (IntVar (-9223372036854775804)),Q (Symbol "a")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (IntVar (-9223372036854775804)),Q (Symbol "a")), target = Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (IntVar (-9223372036854775804)),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (IntVar (-9223372036854775804)),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (IntVar (-9223372036854775804)),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (IntVar (-9223372036854775804)),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (IntVar (-9223372036854775804)),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (IntVar (-9223372036854775804)),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (Symbol "a")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (Symbol "a")), target = Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (Symbol "a"),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "a"),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (Symbol "a"),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "a"),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (Symbol "a"),Q (Symbol "a")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "a"),Q (Symbol "a")), target = Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "a"),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "a"),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (Symbol "a"),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "a"),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (Symbol "a"),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "a"),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (Symbol "a")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (Symbol "a")), target = Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (Symbol "a")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (Symbol "a")), target = Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a")), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "f", fromState = Just (Q (Symbol "b"),Q (IntVar (-9223372036854775804))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "b"),Q (IntVar (-9223372036854775804))), target = Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "b"),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "b"),Q (App (App (Symbol "g") (IntVar (-9223372036854775806))) (Symbol "a"))), target = Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "b"),Q (Symbol "a")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "b"),Q (Symbol "a")), target = Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a")), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "b"),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "b"),Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805)))), target = Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "b"),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "b"),Q (App (App (Symbol "g") (Symbol "b")) (Symbol "a"))), target = Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))), dConstraint = []}

Transition {symbol = "f", fromState = Just (Q (Symbol "b"),Q (Symbol "b")), target = Q (IntVar (-9223372036854775804)), dConstraint = [[([1],[2]),([2],[1])]]}

Transition {symbol = "g", fromState = Just (Q (Symbol "b"),Q (Symbol "b")), target = Q (App (App (Symbol "g") (Symbol "b")) (IntVar (-9223372036854775805))), dConstraint = []}
-}
