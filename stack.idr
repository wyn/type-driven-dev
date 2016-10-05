module Stack

import Data.Vect

%default total


data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)
  
  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height
  
  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 ->
          (a -> StackCmd b height2 height3) ->
          StackCmd b height1 height3

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (s :: stk) Pop = pure (s, stk)
runStack (s :: stk) Top = pure (s, (s :: stk))
runStack stk GetStr = do s <- getLine
                         pure (s, stk)
runStack stk (PutStr s) = do putStr s
                             pure ((), stk)                         
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do (x', stk') <- runStack stk x
                            runStack stk' (f x')

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)
             
doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)                                                                 

data StackIO : Nat -> Type where
  Do : StackCmd a height1 height2 ->
       (a -> Inf (StackIO height2)) -> 
       StackIO height1
       
namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do
                                 
data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run (More fuel) stk (Do c f)
  = do (res, newStk) <- runStack stk c
       run fuel newStk (f res)
run Dry stk p = pure ()


data StkInput = Number Integer | Add


strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput x = if all isDigit $ unpack x
                  then Just $ Number $ cast x
                  else Nothing

mutual 
  
  tryAdd : StackIO height
  tryAdd {height = (S (S h))} = do
    doAdd
    result <- Top
    PutStr (show result ++ "\n")
    stackCalc
  tryAdd = do PutStr "Not enough items in stack, need at least two\n"
              stackCalc
              
  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                   Nothing => do PutStr "Invalid input\n"
                                 stackCalc
                   Just (Number i) => do Push i
                                         stackCalc
                   Just Add => do tryAdd
              
partial                                  
main : IO ()
main = run forever [] stackCalc
