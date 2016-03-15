module Chapt2 

palindrome : String -> Bool
palindrome s = s == reverse s

palindrome2 : String -> Bool
palindrome2 = palindrome . toLower

palindrome3 : Nat -> String -> Bool
palindrome3 n s = length s > n && palindrome s

counts : String -> (Nat, Nat)
counts s = ((length . words) s, length s)

top_ten : (Ord a) => List a -> List a
top_ten ls = take 10 $ sort ls

over_length : Nat -> List String -> Nat
over_length n ls = sum $ map (f n) ls
            where
              f : Nat -> String -> Nat
              f n s = if length s > n then 1 else 0
