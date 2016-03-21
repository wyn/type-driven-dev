module TryIndex

import Data.Vect
import Data.Fin


tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case (integerToFin i n) of
  Nothing => Nothing
  Just idx => Just $ index idx xs
