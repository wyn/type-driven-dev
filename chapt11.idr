module Chapt11

every_other : Stream a -> Stream a
every_other (x :: (y :: xs)) = y :: every_other xs

