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

#eval price_to_tick 5000
#eval price_to_tick 4545
#eval price_to_tick 5500

def q96 : Float := Float.ofNat (2 ^ 96)

#eval q96

def price_to_sqrtp (p : Float) : Float :=
  Float.sqrt p * q96

def sqrtpLow : Float := price_to_sqrtp 4545.0
def sqrtpCur : Float := price_to_sqrtp 5000.0
def sqrtpUpp : Float := price_to_sqrtp 5500.0

#eval sqrtpLow

def order_pair (pa pb: Float) : Float × Float :=
  if pa > pb then (pb, pa) else (pa, pb)

def liquidity0 (amount pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  (amount * (pa * pb) / q96) / (pb - pa)

def liquidity1 (amount pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  amount * q96 / (pb - pa)

def calc_amount0 (liq pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  liq * q96 * (pb - pa) / pa / pb

def calc_amount1 (liq pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  liq * (pb - pa) / q96

def eth : Float := Float.ofNat (10 ^ 18)
def amountEth : Float := 1.0 * eth
def amountUsdc : Float := 5000.0 * eth

def liq0 : Float := liquidity0 amountEth sqrtpCur sqrtpUpp
def liq1 : Float := liquidity1 amountUsdc sqrtpCur sqrtpLow
def liq  : Float := Float.floor (min liq0 liq1)

def amount0 : Float := Float.floor (calc_amount0 liq sqrtpUpp sqrtpCur)
def amount1 : Float := Float.floor (calc_amount1 liq sqrtpLow sqrtpCur)

#eval sqrtpLow
#eval sqrtpCur
#eval sqrtpUpp

#eval liq0
#eval liq1
#eval liq

#eval amount0
#eval amount1
#eval (amount0, amount1)
