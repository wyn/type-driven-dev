module Main

import Data.Vect 


data DataStore : Type where
  MkData : (size : Nat) ->
           (items : Vect size String) ->
           DataStore
           
size : DataStore -> Nat           
size (MkData size items) = size

items : (store : DataStore) -> Vect (size store) String
items (MkData size items) = items

main : IO ()
main = ?main_rhs


