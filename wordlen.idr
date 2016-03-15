import Data.Vect

-- C-c C-l: Load the current file into Idris. A prefix argument causes Idris to only load the portion of the file up to point.
-- C-u C-u C-c C-l: Obliterate the loading marker, switching back to loading the whole buffer.
-- C-c C-n, C-c C-p: Extend and contract the region to be loaded, if such a region exists, one line at a time.
-- C-c C-s: Create an initial pattern match clause for a type declaration
-- C-c C-m: Add missing pattern-match cases to an existing definition
-- C-c C-a: Attempt to solve a hole automatically. A plain prefix argument prompts for hints, while a numeric prefix argument sets the recursion depth.
-- C-c C-e: Extract a hole or provisional definition name to an explicit top level definition
-- C-c C-c: Case split the pattern variable under point, or fill the hole at point with a case expression.
-- C-c C-t: Get the type for the identifier under point. A prefix argument prompts for the name.
-- C-c C-w: Add a with block for the pattern-match clause under point
-- C-c C-h a: Search names, types, and docstrings for a given string.
-- C-c C-z: Pop to a presently open REPL buffer

word_lengths : List String -> List Nat
word_lengths [] = []
word_lengths (word :: words) = length word :: word_lengths words

word_lengths2 : Vect len String -> Vect len Nat
word_lengths2 [] = []
word_lengths2 (x :: xs) = length x :: word_lengths2 xs


total xor : Bool -> Bool -> Bool
xor False x1 = x1
xor True x1 = not x1

isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not $ isEven k

fourInts : Vect 4 Int
fourInts = [1,2,3,4]

sixInts : Vect 6 Int
sixInts = [5,6,7,8,9,10]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts


