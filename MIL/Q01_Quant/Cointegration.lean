import MIL.Common
import Std

open Std
open Lean
open Float
open Array

-- https://uniswapv3book.com/milestone_1/calculating-liquidity.html


example {a b : ℚ} (h1 : a = 1) (h2 : b = 3) : (a + b) / 2 = 2 := by
  linear_combination(h1 + h2) / 2


example {a b : ℚ} (h1 : a ≤ 1) (h2 : b ≤ 3) : (a + b) / 2 ≤ 2 := by
  linear_combination(h1 + h2) / 2

