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

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just $ max x y

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

pi : Double
pi = 3.1415

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture
