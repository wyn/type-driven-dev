module Matrix

import Data.Vect

%default total

create_empties : Vect n (Vect 0 numtype)
create_empties = replicate _ []

transpose_helper :    (x : Vect n numtype) 
                   -> (xs_trans : Vect n (Vect k numtype)) 
                   -> Vect n (Vect (S k) numtype)
transpose_helper [] [] = []
transpose_helper (x :: xs) (y :: ys) = (x :: y) :: transpose_helper xs ys

transpose_mat : (Num numtype) => Vect m (Vect n numtype) -> Vect n (Vect m numtype)
transpose_mat [] = create_empties 
transpose_mat (x :: xs) = let xs_trans = transpose_mat xs in 
                          transpose_helper x xs_trans

transpose_mat2 : (Num numtype) => Vect m (Vect n numtype) -> Vect n (Vect m numtype)
transpose_mat2 [] = create_empties 
transpose_mat2 (x :: xs) = let xs_trans = transpose_mat xs in 
                          zipWith (::) x xs_trans
                          
addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

inner_prod : Num a => Vect m a -> Vect p (Vect m a) -> Vect p a
inner_prod _ [] = []
inner_prod x (y :: ys) = let dotprod = sum $ zipWith (*) x y in 
                         dotprod :: inner_prod x ys

outer_prod : Num a => Vect n (Vect m a) -> Vect p (Vect m a) -> Vect n (Vect p a)
outer_prod [] _ = []
outer_prod _ [] = create_empties
outer_prod (x :: xs) ys = inner_prod x ys :: outer_prod xs ys

multiMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a) 
multiMatrix [] _ = []
multiMatrix xs ys = let ys_trans = transpose_mat ys in
                    outer_prod xs ys_trans 
                           
-- [a,b,c]   A,D,G   [aA+bB+cC, aD+bE+cF, aG+bH+cI]
-- [d,e,f]   B,E,H   [dA+eB+fC, dD+eE+fF, dG+eH+fI]
--           C,F,I
          
-- [a,b,c]   [A,B,C]   [aA+bB+cC, aD+bE+cF, aG+bH+cI]
-- [d,e,f]   [D,E,F]   [dA+eB+fC, dD+eE+fF, dG+eH+fI]
--           [G,H,I]          
          
create_empties1 : Vect n (Vect 0 a)
create_empties1 {n = Z} = []
create_empties1 {n = (S k)} = [] :: create_empties 


