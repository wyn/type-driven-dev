module Chapt4


data Tree a = Empty
            | Node (Tree a) a (Tree a)

%name Tree tree, tree1

insert : Ord a => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right) = case compare x val of
                                      LT => Node (insert x left) val right
                                      EQ => orig
                                      GT => Node left val (insert x right)

listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = let xsTree = listToTree xs in insert x xsTree

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left x right) = (treeToList left ++ [x]) ++ treeToList right

data Expr = I Int
          | EAdd Expr Expr
          | ESub Expr Expr
          | EMult Expr Expr
          
eval : Expr -> Int
eval (I x) = x
eval (EAdd x y) = (eval x) + (eval y)
eval (ESub x y) = (eval x) - (eval y)
eval (EMult x y) = (eval x) * (eval y)

