module Main

import Data.Vect 


data DataStore : Type where
  MkData : (size : Nat) ->
           (items : Vect size String) ->
           DataStore
           

main : IO ()
main = ?main_rhs


