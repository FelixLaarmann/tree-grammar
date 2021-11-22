module Main where
import Term
import RS
import ADC
--import Examples

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
