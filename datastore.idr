module Main

import Data.Vect

  
%default total

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
    
data Command = Add String
             | Get Integer
             | Search String
             | Quit
             | Help
             
parseInput : (cmd : String) -> (args : String) -> Maybe Command
parseInput "add" str = Just (Add str)
parseInput "get" val = case all isDigit (unpack val) of
                            False => Nothing
                            True => Just (Get (cast val))
parseInput "search" substring = Just (Search substring)
parseInput "quit" "" = Just Quit
parseInput "help" "" = Just Help
parseInput _ _ = Nothing                            

parse : (input : String) -> Maybe Command             
parse input = case span (/= ' ') input of
                   (cmd, args) => parseInput cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = 
  let store_items = items store in
    case integerToFin pos (size store) of
      Nothing => Just ("Out of range\n", store)
      Just id => Just (index id store_items ++ "\n", store)

partial
search : DataStore -> String -> List String
search (MkData Z []) substring = []
search (MkData (S k) (item :: items)) substring = case Strings.isInfixOf substring item of
                                                       True => item :: search (MkData k items) substring
                                                       False => search (MkData k items) substring
                      
partial 
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = 
  case parse inp of
    Nothing => Just ("Invalid command\n", store)
    Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
    Just (Get pos) => getEntry pos store
    Just (Search substring) => Just (foldr (++) "" $ intersperse "\n" $ map show (search store substring), store)
    Just Quit => Nothing
    Just Help => Just ("Use [add] [get] [search] commands to add/retrieve/search items in the store.\n" ++
                       "[quit] will quit the session.\n", store)

partial
main : IO ()
main = do
  putStrLn "Enter a command [add] [get] [help] or [quit]"
  replWith (MkData _ []) "Command: " processInput


