module Vect

import Data.Fin

data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : (x : a) -> (xs : Vect k a) -> Vect (S k) a
  
%name Vect xs, ys, zs

append : Vect n a -> Vect m a -> Vect (n+m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

remove' : (i : Fin n) -> Vect n a -> Vect (n - finToNat i) a
remove' FZ xs = xs
remove' (FS j) (x :: xs) = remove' j xs

take' : (i : Fin n) -> Vect n a -> Vect (finToNat i) a
take' FZ xs = []
take' (FS j) (x :: xs) = x :: take' j xs

index : Fin n -> Vect n a -> a
index FZ (x :: xs) = x
index (FS i) (x :: xs) = index i xs


tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         Just idx => Just (index idx xs)

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries pos xs ys = [| (tryIndex pos xs) + (tryIndex pos ys)  |]
