module Main

average : String -> Double
average str = let num_words = word_count str
                  total_length = sum (word_lengths (words str)) in
                  cast total_length / cast num_words
  where
    word_count : String -> Int
    word_count str = cast $ length (words str)
    
    word_lengths : List String -> List Int
    word_lengths strs = map (cast . length) strs          

showAverage : String -> String
showAverage str = "Average word length is: " ++ 
  show (average str) ++ "\n"
  
main : IO ()
main = do
  putStrLn "Enter a string:" 
  s <- getLine
  putStrLn $ showAverage s
