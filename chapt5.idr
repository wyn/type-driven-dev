module Chapt5 

import Data.Vect

read_vect_len : (n : Nat) -> IO (Vect n String)
read_vect_len Z = pure []
read_vect_len (S k) = do
  x <- getLine 
  xs <- read_vect_len k 
  pure (x :: xs)
  
data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a
  
read_vect : IO (len ** Vect len String)
read_vect = do 
  x <- getLine
  if (x == "")
    then pure (_ ** [])
    else do  (_ ** xs) <- read_vect
             pure (_ ** x :: xs)
            
-- note that this gives us a way to extract information 
-- that is baked into the type of vect ie the length            
printVect : Show a => (n ** Vect n a) -> IO ()
printVect (len ** xs) = putStrLn (show xs ++ " (length " ++ show len ++ ")")

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter first vector (blank line to end)"
  (len1 ** xs) <- read_vect
  putStrLn "Enter next vector (blank line to end)"
  (_ ** ys) <- read_vect
  case exactLength len1 ys of
       Nothing => do putStrLn "Input vectors have to be same length"
                     zipInputs
       Just ys' => printVect (len1 ** Data.Vect.zip xs ys')

readToBlank : IO (List String)
readToBlank = do
  x <- getLine
  if x == ""
    then pure []
    else do 
      xs <- readToBlank
      pure (x :: xs)   

readAndSave : IO ()
readAndSave = do
  putStrLn "Enter some data (blank to end)"
  xs <- readToBlank
  putStrLn "Now enter a filename"
  filename <- getLine
  (Right _) <- writeFile filename (foldr (++) "" $ intersperse "\n" xs)
  putStrLn ("Written to: " ++ filename)

readVectFileHandle : (handle : File) -> IO (Either FileError (n ** Vect n String))
readVectFileHandle handle = do
  isEnd <- fEOF handle
  if isEnd 
    then pure (Right (_ ** []))
    else do
      Right line <- fGetLine handle
        | Left err => pure (Left err)
      Right (_ ** lines) <- readVectFileHandle handle
        | Left err => pure (Left err)
      pure (Right (_ ** line :: lines))

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right h <- openFile filename Read
        | Left err => do 
               putStrLn $ show err 
               pure (_ ** [])
  Right xs <- readVectFileHandle h
        | Left err => do 
               putStrLn $ show err 
               pure (_ ** [])
  pure xs

 
