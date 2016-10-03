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
  lbls <- get
  put $ Stream.tail lbls
  right_labelled <- treeLabelWithS right
  pure (Node left_labelled (Stream.head lbls, val) right_labelled)

treeLabelS : Tree a -> Tree (Integer, a)
treeLabelS x = evalState (treeLabelWithS x) [10..]

update : (stateType -> stateType) -> State stateType ()
update f = do
  x <- get
  put $ f x
  
increase' : Nat -> State Nat ()
increase' inc = update (+inc)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = increase' 1
countEmpty (Node left _ right) = do
  countEmpty left
  countEmpty right

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update $ \(x, y) => (x+1, y)
countEmptyNode (Node left _ right) = do
  update $ \ (x, y) => (x, y+1)
  countEmptyNode left
  countEmptyNode right


