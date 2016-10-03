module Chapt12

import Control.Monad.State


labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith lbls [] = []
labelWith (lbl :: lbls) (x :: xs) = (lbl, x) :: labelWith lbls xs

data Tree a = Empty | Node (Tree a) a (Tree a)

testTree : Tree String 
testTree = Node (Node (Node Empty "Jim" Empty) "Fred" 
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty)) 

flattenTree : Tree a -> List a
flattenTree Empty = []
flattenTree (Node left value right) = (flattenTree left) ++ (value :: (flattenTree right))

treeLabelWith : Stream labelType -> Tree a -> 
                (Stream labelType, Tree (labelType, a))
treeLabelWith lbls Empty = (lbls, Empty)
treeLabelWith lbls (Node left val right) = 
  let 
    (this :: lblsLeft, left_labelled) = treeLabelWith lbls left
    (lblsRight, right_labelled) = treeLabelWith lblsLeft right
  in
    (lblsRight, Node left_labelled (this, val) right_labelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = snd $ treeLabelWith [1..] tree

increase : Nat -> State Nat ()
increase inc = do
  current <- get
  put (current + inc)
  
  
treeLabelWithS : Tree a -> State (Stream labelType) (Tree (labelType, a))  
treeLabelWithS Empty = pure Empty
treeLabelWithS (Node left val right) = do 
  left_labelled <- treeLabelWithS left 
  (this :: rest) <- get
  ?pure_Empty
  -- put rest
  -- right_labelled <- treeLabelWithS right
  -- pure (Node left_labelled (this, val) right_labelled)


