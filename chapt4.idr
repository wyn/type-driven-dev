module Chapt4


data Tree a = Empty
            | Node (Tree a) a (Tree a)

%name Tree tree, tree1
