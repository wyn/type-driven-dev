module Chapt10 

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])


describe_help : (Show a) => (input : List a) -> (form : ListLast input) -> String
describe_help [] Empty = "Empty"
describe_help (xs ++ [x]) (NonEmpty xs x) = "Non-empty, inital portion: " ++ xss
              where
                xss : String
                xss = show xs
                
total                
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                     Empty => NonEmpty [] x
                     NonEmpty xs y => NonEmpty (x :: xs) y

describe_list_end_ : List Int -> String
describe_list_end_ xs = describe_help xs (listLast xs)


describe_list_end : List Int -> String
describe_list_end input with (listLast input)
  describe_list_end [] | Empty = "Empty"
  describe_list_end (xs ++ [x]) | (NonEmpty xs x) = "Non-empty, inital value: " ++ show xs
  
my_reverse : List a -> List a  
my_reverse input with (listLast input)
  my_reverse [] | Empty = []
  my_reverse (xs ++ [x]) | (NonEmpty xs x) = x :: my_reverse xs
  
  
data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp : (counter : List a) -> (input : List a) -> SplitList input
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: counter) (item :: items) 
      = case splitListHelp counter items of 
             SplitNil => SplitOne
             SplitOne {x} => SplitPair [item] [x]
             SplitPair lefts rights => SplitPair (item :: lefts) rights
    splitListHelp _ items = SplitPair [] items


merge_sort : Ord a => List a -> List a
merge_sort input with (splitList input)
  merge_sort [] | SplitNil = []
  merge_sort [x] | SplitOne = [x]
  merge_sort (lefts ++ rights) | (SplitPair lefts rights) 
    = merge (merge_sort lefts) (merge_sort rights)


data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)
  
total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs  
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (item :: items) 
  = case takeN k items of 
         Fewer => Exact [item]
         Exact items' => Exact (item :: items')

groupByN : (n : Nat) -> (xs : List a) -> (List (List a))
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)


data SnocList : List a -> Type where
  SnocEmpty : SnocList []
  Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])
  
snocListHelp : SnocList input -> (xs : List a) -> SnocList (input ++ xs)
snocListHelp {input = input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input = input} snoc (x :: xs) = rewrite appendAssociative input [x] xs in snocListHelp (Snoc snoc {x}) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp SnocEmpty xs

total
my_reverse_help : (input : List a) -> SnocList input -> List a
my_reverse_help [] SnocEmpty = []
my_reverse_help (xs ++ [x]) (Snoc rec) = x :: my_reverse_help xs rec

total
my_reverse_snoc : List a -> List a
my_reverse_snoc xs = my_reverse_help xs (snocList xs)

total
my_reverse_snoc2 : List a -> List a
my_reverse_snoc2 input with (snocList input)
  my_reverse_snoc2 [] | SnocEmpty = []
  my_reverse_snoc2 (xs ++ [x]) | (Snoc rec {x}) = x :: my_reverse_snoc2 xs | rec

