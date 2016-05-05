module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar= Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)


record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)


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
--  Search : String -> Command schema
                          
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
parsePrefix SChar item = getQuoted (unpack item)
  where
    getQuoted : List Char -> Maybe (Char, String)
    getQuoted ('"' :: c :: '"' :: rest) = Just (c, ltrim (pack rest))
    getQuoted _ = Nothing
parsePrefix (schema_l .+. schema_r) item = do
  (l_val, item') <- parsePrefix schema_l item
  (r_val, item'') <- parsePrefix schema_r item'
  return  ((l_val, r_val), item'')

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
parseSchema ("Char" :: xs) = case xs of
                                  [] => Just SChar
                                  _ => case parseSchema xs of
                                            Nothing => Nothing
                                            Just xs' => Just (SChar .+. xs')
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

-- parseInput schema "search" substring = Just (Search substring)
parseInput schema "quit" "" = Just Quit
parseInput schema "help" "" = Just Help
parseInput _ _ _ = Nothing                            

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseInput schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (a, b) = display a ++ ", " ++ display b

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = 
  let store_items = items store in
    case integerToFin pos (size store) of
      Nothing => Just ("Out of range\n", store)
      Just id => Just (display (index id store_items) ++ "\n", store)

-- search : DataStore -> String -> List String
-- search (MkData schema Z []) substring = []
-- search (MkData schema (S k) (item::items)) substring = ?search_rhs_3

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
    Just Help => Just ("Use [add] [get] commands to add/retrieve items in the store.\n" ++
                       "[quit] will quit the session.\n", store)

-- partial
main : IO ()
main = do
  putStrLn "Enter a command [add] [get] [help] or [quit]"
  replWith (MkData SString _ []) "Command: " processInput


test : Maybe (String, DataStore)
test = do
  let ds = MkData SString _ []
  (_, ds1) <- processInput ds "schema Int String Char String" 
  (_, ds2) <- processInput ds1 "add 1 \"simon\" \"w\" \"parry\""
  (_, ds3) <- processInput ds2 "get 0"
  return ("done", ds3)  

