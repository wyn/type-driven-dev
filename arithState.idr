module ArithState 


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

runCommand : Command a -> IO a
runCommand (PutStr x) = putStrLn x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do x' <- runCommand x
                           runCommand (f x')
runCommand (PutGameState x) = ?runCommand_rhs_1
runCommand GetGameState = ?runCommand_rhs_2
runCommand GetRandom = ?runCommand_rhs_3

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit val) = do pure (Just val) 
run (More fuel) (Do x f) = do x' <- runCommand x
                              run fuel (f x')
run Dry y = pure Nothing


mutual 
  correct : ConsoleIO GameState
  correct = ?correct_rhs

  wrong : Int -> ConsoleIO GameState
  wrong ans = ?wrong_rhs
  
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
