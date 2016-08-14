module Chapt11

%default total

every_other : Stream a -> Stream a
every_other (x :: (y :: xs)) = y :: every_other xs

data InfList : Type -> Type where
  (::) : (value :elem) -> Inf (InfList elem) -> InfList elem
  
%name InfList xs, ys, zs

Functor InfList where
  map func (x :: xs) = func x :: (map func xs)

countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x+1)

getPrefix : (n : Nat) -> InfList a -> List a
getPrefix Z xs = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

