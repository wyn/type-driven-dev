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

addToStore : DataStore -> String -> DataStore 
addToStore (MkData size items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (item :: items') = item :: addToData items'
    

main : IO ()
main = ?main_rhs


