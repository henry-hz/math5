import MIL.Common
import Std

open Std
open Lean
open Float
open Array

-- https://uniswapv3book.com/milestone_1/calculating-liquidity.html


def natArray : Array ℕ    := #[0, 1, 2]
def m : Array ℕ := range 100



noncomputable def iC := Real.log (Real.sqrt 1.0001) * 70.71



def i2 := log (sqrt 1.0001) * 70.71
#eval i2




-- floor is necessary because ticks are integers
def price_to_tick (p : Float) : Float :=
  floor (log p / log 1.0001)

#eval priceToTick 5000
#eval priceToTick 4545
#eval priceToTick 5500


def q96:Float := 2^96

#eval q96

def price_to_sqrtp (p: Float) : Float :=
  sqrt p * q96

#eval

