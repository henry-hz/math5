import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common
import Std

open Std
open Lean
open Nat


namespace B00_Fun


example : 3 * 23 = 23 * 3 := by rfl

def twice (f : ℕ → ℕ) (a: ℕ) :=
  f (f a)


#eval twice (λ x => x + 3) 10

theorem twice_add (a : ℕ) : twice (λ x => x + 2) a = a + 4 := by
  rfl


theorem eq_proof: (5 - 2 = 3) = ( 5 = 2 + 3) :=
  calc
    (5 - 2 = 3) = (5 = 2 + 3) := by ring_nf


-- Define the theorem to prove
theorem five_minus_two_equals_three : 5 - 2 = 3 := by
  rfl

-- Define the theorem to prove
theorem five_equals_two_plus_three : 5 = 2 + 3 := by
  rfl

-- Define the proof that the expressions are equivalent
-- theorem equivalence_proof : five_minus_two_equals_three = five_equals_two_plus_three := by

theorem diff2 {z y : ℤ} (h1: z = 3 - 5) (h2: y = 9) : y + z < 10 := by
  calc
  y + z = y + z    := by ring
  _ = 9 + z        := by rw [h2]
  _ = 9 + (3 - 5)  := by rw [h1]
  _ = 7            := by ring
  _ < 10           := by simp  -- TODO: continue using more specific tactic

-- if a is positive, it's opposite is (-1) * a = - a, this means that the
-- product of any positive number and any negative number is negative
-- [made by gpt - FIXME]
theorem pos {a b : ℤ} : a > 0 → b < 0 → a * b < 0 := by
  intro ha hb
  have h1 : a * b < a * 0 := by
    apply mul_lt_mul_of_pos_left hb ha
  have h2 : a * 0 = 0 := by
    apply mul_zero
  have h3 : a * b < 0 := by
    rw [h2] at h1
    exact h1
  exact h3



example (r s : ℝ) (h1: r + 2 * s = -1) (h2: s = 3) : r = -7  :=
  calc
  r = r + 2 * s - 2 * s := by ring
  _ = -1 - 2 * s        := by rw [h1]
  _ = -1 - 2 * 3        := by rw [h2]
  _ = -7                := by ring
