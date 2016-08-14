module Chapt11

import Data.Primitives.Views


%default total

every_other : Stream a -> Stream a
every_other (x :: (y :: xs)) = y :: every_other xs

data InfList : Type -> Type where
  (::) : (value :elem) -> Inf (InfList elem) -> InfList elem
  
%name InfList xs, ys, zs

Functor InfList where
  map func (x :: xs) = func x :: (map func xs)

countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x+1)

getPrefix : (n : Nat) -> InfList a -> List a
getPrefix Z xs = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

data Face = Heads | Tails

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
               (seed' `shiftR` 2) :: randoms seed'

getFace : Int -> Face
getFace x with (divides x 2)
  getFace ((2 * div) + rem) | (DivBy prf) = 
    if rem == 0 then Heads else Tails
    
coinFlips : (count : Nat) -> Stream Int -> List Face  
coinFlips Z xs = []
coinFlips (S k) (x :: xs) = getFace x :: (coinFlips k xs)

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx = let next = (approx + (number / approx)) / 2 in 
                                   approx :: (square_root_approx number next)
                                   
square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) -> (approxs : Stream Double) -> Double
square_root_bound Z number bound (x :: xs) = x
square_root_bound (S k) number bound (x :: xs) = let err = abs (number - (x*x)) in
                                                 if err < bound then x 
                                                 else square_root_bound k number bound xs
                                                 
square_root : (number : Double) -> Double                                                 
square_root number = square_root_bound 100 number 0.0000000001 
                     (square_root_approx number number)

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> ( a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> InfIO -> IO ()
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)
run Dry _ = putStrLn "out of fuel"

partial
forever : Fuel
forever = More forever

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = Do (do putStrLn prompt
                                 s <- getLine
                                 putStrLn (action s)) 
                             (\ _ => totalREPL prompt action)




