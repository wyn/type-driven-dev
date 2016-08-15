module Chapt11

import Data.Primitives.Views
import System


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

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1


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

namespace CommandDo
  data Command : Type -> Type where
    PutStr : String -> Command ()
    GetLine : Command String
    Pure : ty -> Command ty
    Bind : Command a -> (a -> Command b) -> Command b
    
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

  data Input = Answer Int | QuitCmd
  
  readInput : (prompt : String) -> Command Input  
  readInput prompt = do PutStr prompt
                        answer <- GetLine
                        if toLower answer == "quit" 
                        then Pure QuitCmd
                        else Pure (Answer (cast answer))
  
namespace ConsoleDo
  data ConsoleIO : Type -> Type where
    Quit : a -> ConsoleIO a
    Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do
  
  runCommand : Command a -> IO a
  runCommand (PutStr x) = putStr x
  runCommand GetLine = getLine
  runCommand (Pure val) = pure val
  runCommand (Bind c f) = do res <- runCommand c
                             runCommand (f res)
                             
  run : Fuel -> ConsoleIO a -> IO (Maybe a)
  run _ (Quit y) = do pure (Just y)
  run (More fuel) (Do c f) = do res <- runCommand c
                                run fuel (f res)
  run Dry (Do z f) = pure Nothing


mutual
  correct : Stream Int -> (score : Nat) -> ConsoleIO Nat
  correct xs score = do PutStr "Correct\n" 
                        quiz xs (score+1)
  
  wrong : Stream Int -> Int -> (score : Nat) -> ConsoleIO Nat
  wrong xs x score = do PutStr ("Wrong, the answer is " ++ show x ++ "\n")
                        quiz xs score
  
  quiz : Stream Int -> (score : Nat) -> ConsoleIO Nat
  quiz (num1 :: num2 :: nums) score 
    = do PutStr ("Score so far: " ++ show score ++ "\n")
         input <- readInput (show num1 ++ " * " ++ show num2 ++ "?\n")
         case input of
           Answer answer => if (answer == num1 * num2) 
                               then correct nums score
                               else wrong nums (num1 * num2) score
           QuitCmd => Quit score

partial
main : IO ()
main = do seed <- time
          Just score <- ConsoleDo.run forever (quiz (arithInputs (fromInteger seed)) 0)
                     | Nothing => putStrLn ("Out of fuel")
          putStrLn ("Final score: " ++ show score)
