module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)


record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

-- schema : DataStore -> Schema
-- schema (MkData schema' size items) = schema'

-- size : DataStore -> Nat           
-- size (MkData schema size items) = size

-- items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
-- items (MkData schema size items) = items


addToStore : (store : DataStore) -> SchemaType (schema store)  -> DataStore 
addToStore (MkData schema size items) newitem = MkData schema _ (addToData items)
  where
    addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    addToData [] = [newitem]
    addToData (item :: items') = item :: addToData items'
    
data Command : Schema -> Type where
  SetSchema : (newschema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  Quit : Command schema
  Help : Command schema

--              | Search String
                          
parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)                          
parsePrefix SString item = getQuoted (unpack item)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) = case span (/= '"') xs of
                                 (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                                 _ => Nothing
    getQuoted _ = Nothing
    
parsePrefix SInt item = case span isDigit item of
                             ("", rest) => Nothing
                             (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schema_l .+. schema_r) item = case parsePrefix schema_l item of
                                                Nothing => Nothing
                                                Just (l_val, item') => 
                                                case parsePrefix schema_r item' of
                                                     Nothing => Nothing
                                                     Just (r_val, item'') => Just ((l_val, r_val), item'')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of 
                                  Just (res, "") => Just res
                                  Just _ => Nothing
                                  Nothing => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) = case xs of
                                      [] => Just SString
                                      _ => case parseSchema xs of
                                                Nothing => Nothing
                                                Just xs' => Just (SString .+. xs')
parseSchema ("Int" :: xs) = case xs of
                                 [] => Just SInt
                                 _ => case parseSchema xs of
                                           Nothing => Nothing
                                           Just xs' => Just (SInt .+. xs')

parseInput : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseInput schema "add" str = case parseBySchema schema str of
                                   Nothing => Nothing
                                   Just rest => Just (Add rest)
parseInput schema "get" val = case all isDigit (unpack val) of
                            False => Nothing
                            True => Just (Get (cast val))
parseInput schema "schema" rest = case parseSchema (words rest) of
                                       Nothing => Nothing
                                       Just schema_ok => Just (SetSchema schema_ok)

-- parseInput "search" substring = Just (Search substring)
parseInput schema "quit" "" = Just Quit
parseInput schema "help" "" = Just Help
parseInput _ _ _ = Nothing                            

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseInput schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (a, b) = display a ++ ", " ++ display b

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = 
  let store_items = items store in
    case integerToFin pos (size store) of
      Nothing => Just ("Out of range\n", store)
      Just id => Just (display (index id store_items) ++ "\n", store)

-- search : DataStore -> String -> List String
-- search (MkData Z []) substring = []
-- search (MkData (S k) (item :: items)) substring = case Strings.isInfixOf substring item of
--                                                        True => item :: search (MkData k items) substring
--                                                        False => search (MkData k items) substring

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              S k => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = 
  case parse (schema store) inp of
    Nothing => Just ("Invalid command\n", store)
    Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
    Just (Get pos) => getEntry pos store
    Just (SetSchema schema') => case setSchema store schema' of
                                     Nothing => Just ("Cannot reset schema\n", store)
                                     Just store' => Just ("OK\n", store')
--    Just (Search substring) => Just (foldr (++) "" $ intersperse "\n" $ map show (search store substring), store)
    Just Quit => Nothing
    Just Help => Just ("Use [add] [get] [search] commands to add/retrieve/search items in the store.\n" ++
                       "[quit] will quit the session.\n", store)

-- partial
main : IO ()
main = do
  putStrLn "Enter a command [add] [get] [help] or [quit]"
  replWith (MkData SString _ []) "Command: " processInput


