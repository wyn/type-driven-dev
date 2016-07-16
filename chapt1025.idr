module Chapt1025 

import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views


total
equalSuffix : (Eq a) => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (xs ++ [x]) ys | (Snoc xrec) with (snocList ys)
    equalSuffix (xs ++ [x]) [] | (Snoc xrec) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xrec) | (Snoc yrec) 
      = if x == y then (equalSuffix xs ys | xrec | yrec) ++ [x]
                  else []
                  
total
merge_sort : Ord a => Vect n a -> Vect n a
merge_sort xs with (splitRec xs)
  merge_sort [] | SplitRecNil = []
  merge_sort [x] | SplitRecOne = [x]
  merge_sort (ls ++ rs) | (SplitRecPair lrec rrec) 
    = merge (merge_sort ls | lrec) (merge_sort rs | rrec) 

total
toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

-- 2 = 1 + 1     = '  10'  = '1'         +   '0'
-- 3 = S (1 + 1) = '  11'  = '1'         +   '1'
-- 4 = 2 + 2     = ' 100'  = '10' + '10' +   '0'
-- 5 = S (2 + 2) = ' 101'  = '10' + '10' +   '1'
-- 6 = 3 + 3     = ' 110'  = '11' + '11' +   '0'
-- 7 = S (3 + 3) = ' 111'  = '11' + '11' +   '1'                
-- 8 = 4 + 4     = '1000' = '100' + '100' +  '0'
-- 9 = S (4 + 4) = '1001' = '100' + '100' +  '1'

total
palindrome : List Char -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) 
    = if x == y then (palindrome ys | rec) else False

