module Chapt8


data MyVect : Nat -> Type -> Type where
  Nil : MyVect Z a
  (::) : a -> MyVect k a -> MyVect (S k) a
  
  
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

exactLength : (len : Nat) -> (input : MyVect m a) -> Maybe (MyVect len a)
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

my_plusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
my_plusCommutes Z Z = Refl
my_plusCommutes Z (S k) = rewrite my_plusCommutes Z k in Refl
my_plusCommutes (S k) Z = plusZeroRightNeutral (S k)
my_plusCommutes (S k) (S j) = let inductive_prf = my_plusCommutes k j in
                                  rewrite sym $ plusSuccRightSucc k j in 
                                    rewrite inductive_prf in 
                                      rewrite plusSuccRightSucc j k in 
                                        Refl

my_reverse : MyVect n a -> MyVect n a
my_reverse xs = reverse' [] xs
  where reverse' : MyVect n a -> MyVect m a -> MyVect (n+m) a
        reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
        reverse' {n} {m=(S k)} acc (x :: xs) 
          = let stuff = (reverse' (x::acc) xs) in
                rewrite sym $ plusSuccRightSucc n k in stuff

twoplustwo_not_five : 2 + 2 = 5 -> Void
twoplustwo_not_five Refl impossible

head_unequal : DecEq a => {xs : MyVect n a} -> {ys : MyVect n a} ->
       (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void       
head_unequal contra Refl = contra Refl


tail_unequal : DecEq a => {xs : MyVect n a} -> {ys : MyVect n a} ->
              (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tail_unequal contra Refl = contra Refl


-- didn't understand how to get this answer incrementally
-- ended up looking at Vect impl
DecEq a => DecEq (MyVect n a) where  
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys) | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (x :: xs) (x :: ys) | Yes Refl | No contra = No (tail_unequal contra)
    decEq (x :: xs) (y :: ys) | No contra = No (head_unequal contra)

