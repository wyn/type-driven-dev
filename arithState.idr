module ArithState 

import Data.Primitives.Views
import System


record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat
  
record GameState where
  constructor MkGameState
  score : Score
  difficulty : Nat
  
initState : GameState
initState = MkGameState (MkScore 0 0) 12

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++ 
              "Difficulty: " ++ show (difficulty st)


addWrong : GameState -> GameState
addWrong state
    = record { score->attempted = attempted (score state) + 1 } state

addCorrect : GameState -> GameState
addCorrect state
  = record { score->correct = correct (score state) + 1,
             score->attempted = attempted (score state) + 1 } state
                       
-- addWrong : GameState -> GameState
-- addWrong = record { score->attempted $= (+1) }

-- addCorrect : GameState -> GameState
-- addCorrect = record { score->correct $= (+1),
--                       score->attempted $= (+1) }
                        
                                                                      
data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  
  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()
             
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b
  
data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  
namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind
  
  Functor Command where
      map func x = Bind x (\val => Pure (func val))
  
  Applicative Command where
    pure = Pure
    (<*>) f x = Bind f (\f' => map f' x)
  
  Monad Command where
    (>>=) = Bind

  
namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do


data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

-- runCommand : Command a -> IO a
-- runCommand (PutStr x) = putStrLn x
-- runCommand GetLine = getLine
-- runCommand (Pure x) = pure x
-- runCommand (Bind x f) = do x' <- runCommand x
--                            runCommand (f x')
-- runCommand (PutGameState x) = ?runCommand_rhs_1
-- runCommand GetGameState = ?runCommand_rhs_2
-- runCommand GetRandom = ?runCommand_rhs_3

-- run : Fuel -> ConsoleIO a -> IO (Maybe a)
-- run _ (Quit val) = do pure (Just val) 
-- run (More fuel) (Do x f) = do x' <- runCommand x
--                               run fuel (f x')
-- run Dry y = pure Nothing

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = do st <- GetGameState 
                       PutGameState (f st)

mutual 
  correct : ConsoleIO GameState
  correct = do PutStr "Correct\n"
               updateGameState addCorrect
               quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
                 updateGameState addWrong
                 quiz
  
  data Input = Answer Int
               | QuitCmd  
  
  readInput : (prompt : String) -> Command Input
  readInput prompt = do PutStr prompt
                        answer <- GetLine
                        if toLower answer == "quit"
                          then Pure QuitCmd
                          else Pure (Answer (cast answer))  
  
  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")
            input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
            case input of
              Answer answer => if answer == num1 * num2
                               then correct
                               else wrong (num1 * num2)
              QuitCmd => Quit st
              
runCommand : Stream Int ->
             GameState ->
             Command a ->
             IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do putStrLn x
                                      pure ((), rnds, state)
runCommand rnds state GetLine = do x <- getLine
                                   pure (x, rnds, state)
runCommand (rnd :: rnds) state GetRandom = 
  pure (getRandom rnd (fromNat $ difficulty state), rnds, state)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1

runCommand rnds state GetGameState = pure (state, rnds, state)
runCommand rnds state (PutGameState state') = pure ((), rnds, state')
runCommand rnds state (Pure x) = pure (x, rnds, state)
runCommand rnds state (Bind x f) = do (x', rnds', state') <- runCommand rnds state x
                                      runCommand rnds' state' (f x')

run : Fuel -> Stream Int -> GameState -> ConsoleIO a ->
      IO (Maybe a, Stream Int, GameState)
                                               
run fuel rnds state (Quit val) = do pure (Just val, rnds, state)
run (More fuel) rnds state (Do c f) = do 
  (val, rnds', state') <- runCommand rnds state c 
  run fuel rnds' state' (f val)
run Dry rnds state _ = pure (Nothing, rnds, state)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

partial
main : IO ()
main = do 
  seed <- time
  (Just score, _, state) <- run forever (randoms (fromInteger seed)) initState quiz
                                | _ => putStrLn "Ran out of fuel"
  putStrLn ("Final score: " ++ show state)
