import Data.Vect

inserter : (Ord elem') => (x : elem') -> (xs_sorted : Vect n elem') -> Vect (S n) elem'
inserter x [] = [x]
inserter x (y :: xs) = case x < y of
                            False => y :: inserter x xs
                            True  => x :: y :: xs

ins_sort : (Ord elem') => Vect n elem' -> Vect n elem'
ins_sort [] = []
ins_sort (x :: xs) = let xs_sorted = ins_sort xs in
                         inserter x xs_sorted

my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs

my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = ?reversed

my_map : (a -> b) -> List a -> List b                 
my_map f [] = []
my_map f (x :: xs) = f x :: my_map f xs

my_map2 : (a -> b) -> Vect n a -> Vect n b                 
my_map2 f [] = []
my_map2 f (x :: xs) = f x :: my_map2 f xs


