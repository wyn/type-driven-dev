module Main

import chapt2
              
main : IO ()
main = do
  putStrLn "Enter a phrase"
  ln <- getLine
  putStrLn $ if palindrome ln then
               ln ++ " is a palindrome"
             else
               ln ++ " is not a palindrome"
