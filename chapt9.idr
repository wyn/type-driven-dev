module Chapt9

import Data.Vect

removeElem' : (DecEq a) => (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem' value (value :: xs) Here = xs
removeElem' {n = Z} value (x :: []) (There later) = absurd later
removeElem' {n = (S k)} value (x :: xs) (There later) = x :: removeElem' value xs later

not_in_nil : Elem value [] -> Void
not_in_nil Here impossible
not_in_nil (There _) impossible

not_in_tail : (notThere : Elem value xs -> Void) -> 
              (notHere : (value = x) -> Void) -> 
              Elem value (x :: xs) -> Void
not_in_tail notThere notHere Here = notHere Refl
not_in_tail notThere notHere (There later) = notThere later

isElem' : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)     
isElem' value [] = No not_in_nil
isElem' value (x :: xs) = case decEq value x of
                         Yes Refl => Yes Here
                         No cont => (case isElem' value xs of
                                          (Yes prf) => Yes (There prf)
                                          (No contra) => No (not_in_tail contra cont))


maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

