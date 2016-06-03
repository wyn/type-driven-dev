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

data Last : List a -> a -> Type where
    LastOne : Last [item] value
    LastCons : (prf : Last xs value) -> Last (x :: xs) value

not_last_of_nil : Last [] value -> Void
not_last_of_nil LastOne impossible
not_last_of_nil (LastCons _) impossible


-- not_last_one : (cont : (x = value) -> Void) -> 
--                Last (x :: []) value -> Void
-- not_last_one cont LastOne = ?absurd_LastOne
-- not_last_one _ (LastCons LastOne) impossible
-- not_last_one _ (LastCons (LastCons _)) impossible


not_last_but_one : (contr : Last (y :: xs) value -> Void) -> 
                   Last (x :: (y :: xs)) value -> Void
not_last_but_one contr (LastCons prf) = contr prf



not_last_one : (not_there : Last [] value -> Void) -> 
               (not_here : (x = value) -> Void) -> 
               Last [x] value -> Void
not_last_one not_there not_here LastOne = not_here ?not_last_one_rhs_2
not_last_one _ _ (LastCons LastOne) impossible
not_last_one _ _ (LastCons (LastCons _)) impossible

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No not_last_of_nil
isLast (x :: []) value = case decEq x value of
                         Yes Refl => Yes LastOne
                         No cont => case isLast [] value of 
                                    No contr => No (not_last_one contr cont)
--             No (not_last_one cont)
isLast (x :: (y :: xs)) value = case isLast (y :: xs) value of 
                                Yes prf => Yes (LastCons prf) 
                                No contr => No (not_last_but_one contr)



-- -- isLast (x :: []) value with (decEq x value)
-- --   isLast (x :: []) x     | Yes Refl = Yes LastOne
-- --   isLast (x :: []) value | No contr = No (not_last_one contr)   
