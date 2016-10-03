module TreeLabelType 

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()
  
  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b


get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

Functor (State s) where
    map func x = Bind x (\val => Pure (func val))

Applicative (State s) where
    pure = Pure
    (<*>) f x = Bind f (\func => map func x) 

Monad (State s) where
    (>>=)  = Bind


data Tree a = Empty | Node (Tree a) a (Tree a)

testTree : Tree String 
testTree = Node (Node (Node Empty "Jim" Empty) "Fred" 
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty)) 

flattenTree : Tree a -> List a
flattenTree Empty = []
flattenTree (Node left value right) = (flattenTree left) ++ (value :: (flattenTree right))

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left val right)
     = do left_labelled <- treeLabelWith left
          (this :: rest) <- get
          put rest
          right_labelled <- treeLabelWith right
          pure (Node left_labelled (this, val) right_labelled)

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put x) st = ((), x)
runState (Pure x) st = (x, st)
runState (Bind x f) st = let (val, st') = runState x st in
                         runState (f val) st'

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = fst (runState (treeLabelWith tree) [1..])


addIfPositive : Integer -> State Integer Bool
addIfPositive val = do when (val > 0) $ 
                            do current <- get
                               put (current + val)
                       pure (val > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do added <- traverse addIfPositive xs
                     pure $ length $ filter id added


