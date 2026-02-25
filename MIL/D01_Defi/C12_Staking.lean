import Mathlib.Data.Real.Basic
import MIL.Common
import Std
import Mathlib.Data.Real.Sqrt

open Real


open Std
open Lean
open Nat
open Array


def WAD : ℕ := 10 ^ 18
def RAY : ℕ := 10 ^ 27

def a : ℕ := 2
def b : ℕ := 1000

def c : ℕ := a * WAD/ b

#eval c
#eval c * 7
#eval c / 7
def z := c + (9*WAD)
def z1 := (z * c) / WAD
#eval z1



def d : ℕ := (c * 7)


#eval a*WAD/b


#eval WAD


example (x : ℝ) (h : 0 ≤ x) : √x * √x = x :=
  mul_self_sqrt h



def p1 : ℝ := 4
def x : ℝ := 9
#eval Real.sqrt x   -- √9 = 3.0 (numerical evaluation)

-- The current tick corresponds to the current price
-- (5000 USDC for 1 ETH).
def currentPrice : ℝ := 5000

-- The lower and upper bounds of the price range
-- into which liquidity is provided.
def lowerPrice : ℝ := 4545
def upperPrice : ℝ := 5500


namespace UniswapV3Book.M1

open Real

/-
In the book chapter, `P` is the *square-root price* (since √5000 ≈ 70.71, etc.).
Ticks map to sqrt-price via: P(i) = 1.0001^(i/2)
and i = log_{1.0001}(P).
-/

/-- Tick base used by Uniswap v3. -/
def tickBase : ℝ := 1.0001

/-- sqrt-price at tick `i`:  P(i) = 1.0001^(i/2). -/
def sqrtPriceOfTick (i : ℤ) : ℝ :=
  Real.rpow tickBase ((i : ℝ) / 2)

/-- Tick for sqrt-price `p`:  i = ⌊ log(p) / log(1.0001) ⌋. -/
def tickOfSqrtPrice (p : ℝ) : ℤ :=
  Int.floor (Real.log p / Real.log tickBase)

/- Example sqrt-prices from the page -/
def Pc : ℝ := Real.sqrt 5000   -- current
def Pl : ℝ := Real.sqrt 4545   -- lower
def Pu : ℝ := Real.sqrt 5500   -- upper

/-- Example ticks (floored). -/
def ic : ℤ := tickOfSqrtPrice Pc
def il : ℤ := tickOfSqrtPrice Pl
def iu : ℤ := tickOfSqrtPrice Pu

/-
Q64.96 encoding: multiply a sqrt-price by 2^96 and floor to an integer.
-/
def Q96 : ℕ := 2 ^ 96
def q96 : ℝ := (Q96 : ℝ)

/-- Encode sqrt(price) as Q64.96 (aka sqrtPriceX96). -/
def sqrtPriceX96 (price : ℝ) : ℕ :=
  ((Real.sqrt price) * q96).floor.toNat

def PcX96 : ℕ := sqrtPriceX96 5000
def PlX96 : ℕ := sqrtPriceX96 4545
def PuX96 : ℕ := sqrtPriceX96 5500

/-
Core relations from the chapter:

Δx = (1/Pc - 1/Pb) * L
Δy = (Pc - Pa) * L

Solve for L:

L = Δx * (Pb*Pc) / (Pb - Pc)
L = Δy / (Pc - Pa)

Then compute two L's and take min.
-/

/-- Δx = (1/Pc - 1/Pb) * L. -/
def deltaX (L Pc Pb : ℝ) : ℝ :=
  (1 / Pc - 1 / Pb) * L

/-- Δy = (Pc - Pa) * L. -/
def deltaY (L Pc Pa : ℝ) : ℝ :=
  (Pc - Pa) * L

/-- L from Δx: L = Δx * (Pb*Pc)/(Pb - Pc). -/
def liquidityFromDeltaX (dx Pc Pb : ℝ) : ℝ :=
  dx * (Pb * Pc) / (Pb - Pc)

/-- L from Δy: L = Δy/(Pc - Pa). -/
def liquidityFromDeltaY (dy Pc Pa : ℝ) : ℝ :=
  dy / (Pc - Pa)

/-
Same computations but in the Q64.96 integer style shown in the page’s Python:

liquidity0(amount, pa, pb) = (amount * (pa*pb)/Q96) / (pb - pa)
liquidity1(amount, pa, pb) = amount * Q96 / (pb - pa)

and the inverse:

amount0 = L * Q96 * (pb - pa) / pa / pb
amount1 = L * (pb - pa) / Q96
-/

/-- Ensure (pa,pb) are ordered. -/
def ordered (pa pb : ℕ) : ℕ × ℕ := (min pa pb, max pa pb)

/-- L from token0 amount (Q96 style). -/
def liquidity0X96 (amount pa pb : ℕ) : ℕ :=
  let (lo, hi) := ordered pa pb
  ((amount * ((lo * hi) / Q96)) / (hi - lo))

/-- L from token1 amount (Q96 style). -/
def liquidity1X96 (amount pa pb : ℕ) : ℕ :=
  let (lo, hi) := ordered pa pb
  (amount * Q96) / (hi - lo)

/-- token0 amount from L (Q96 style). -/
def amount0FromLiquidityX96 (L pa pb : ℕ) : ℕ :=
  let (lo, hi) := ordered pa pb
  (L * Q96 * (hi - lo)) / lo / hi

/-- token1 amount from L (Q96 style). -/
def amount1FromLiquidityX96 (L pa pb : ℕ) : ℕ :=
  let (lo, hi) := ordered pa pb
  (L * (hi - lo)) / Q96

end UniswapV3Book.M1
