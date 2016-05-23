module Chapt8


data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a
  
  
data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num
  
  
sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)  
sameS k k (Same k) = Same (S k)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of 
                              Nothing  => Nothing
                              Just eq  => Just (sameS k j eq)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat m len of
                                 Nothing => Nothing 
                                 Just (Same m) => Just input

same_cons : {xs : List a} -> {ys : List a} -> 
            xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf

same_lists : {xs : List a} -> {ys : List a} -> 
             x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl prfs = same_cons prfs

data ThreeEq : (a : Nat) -> (b : Nat) -> (c : Nat) -> Type where
  SameThree : (x : Nat) -> ThreeEq x x x
  
allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x (SameThree x) = SameThree (S x)






 
 
 
 
 
