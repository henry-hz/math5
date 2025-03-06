import Mathlib.Data.Real.Basic
import MIL.Common
import Std

open Std
open Lean
open Nat
open Array


def leverage (total: ℚ) (margin: ℚ) : ℚ :=
  total / margin

#eval leverage 9 3

-- For instance, let's consider a futures contract with a total
-- value of $80,000 and an initial margin requirement of $4,000.
-- According to the calculation provided in 0, the leverage
-- should be 20, which is the inverse of the margin requirement (1 / 0.05).

example : leverage 80000 4000 = 20 := by rfl
