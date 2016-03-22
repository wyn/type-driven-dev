module Chapt42

%default total

data PowerSource = Petrol | Pedal | Electric

data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Unicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Motorbike : (fuel : Nat) -> Vehicle Petrol
  
wheels : Vehicle powertype -> Nat
wheels Bicycle = 2
wheels Unicycle = 4
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels (Motorbike fuel) = 2

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorbike fuel) = Motorbike 50

