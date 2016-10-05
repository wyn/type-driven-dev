module Chapt13

namespace Guess
  data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S guesses) guesses
    Pure : ty -> GuessCmd ty state state
    (>>=) : GuessCmd a state1 state2 ->
            (a -> GuessCmd b state2 state3) ->
            GuessCmd b state1 state3

three_guesses: GuessCmd () 3 0
three_guesses = do Try 10
                   Try 20
                   Try 15
                   Pure ()

  -- no_guesses : GuessCmd () 0 0
  -- no_guesses = do Try 10
  --                 Pure ()


namespace Physics
  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
    Melt : MatterCmd () Solid Liquid
    Boil : MatterCmd () Liquid Gas
    Condense : MatterCmd () Gas Liquid
    Freeze : MatterCmd () Liquid Solid
  
    Pure : ty -> MatterCmd ty state state
    (>>=) : MatterCmd a state1 state2 ->
            (a -> MatterCmd b state2 state3) ->
            MatterCmd b state1 state3
  
ice_steam : MatterCmd () Solid Gas
ice_steam = do Melt
               Boil
               
steam_ice : MatterCmd () Gas Solid
steam_ice = do Condense
               Freeze


-- over_melt : MatterCmd () Solid Liquid
-- over_melt = do Melt
--                Melt
