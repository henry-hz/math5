import Mathlib
import Init.Data.Nat.Basic

open Real


-- # Intro
-- dependently-typed language


#check 2
#check 14 + 3
#check π

#check ℕ
#check Type
#check Type 1
#check Type 2
#check Type 3
#check ℝ

def j : ℕ := 3

def y : ℕ  := sorry
#check y

example : ℕ := 2

#check (2 + 3 = 23) = false
#check rexp 3
#check rexp (1 + π)
#check rexp 1 < π
def a : ℕ := 3
#check a = j
#check Irrational 3

def m1 : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)
def m2 : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)
def m3 : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)
#check m1
#check m3

example : 2 + 2 = 2 + 1 + 1 := by ring
example : 2 + 2 = 2 + 1 + 1 := by rfl
example : 2 + 2 ≠ 5 := by simp
example : ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry

example : True := by trivial
example : 2 = 2 := by rfl
example (a b : ℕ) : a + b = b + a := by ring
example (a b : ℕ) : a + b = b + a := by rw[Nat.add_comm]


-- write my proposition [and after we will write a proof]
-- that every natural number has an upper bound
def my_prop : Prop := ∀ n : ℕ, ∃ p, n ≤ p
theorem mp' : my_prop := fun n => ⟨n, le_rfl⟩


-- ugly manual proof
example (a b : ℕ) : a + a * b = (b + 1) * a :=
  (add_comm a (a * b)).trans
  ((mul_add_one a b).symm.trans
  (mul_comm a (b + 1)))


-- proof using a ring, that generate a proof by its own
--
example (a b : ℕ) : a + a * b = (b + 1) * a := by ring
example : 2 + 2 ≠ 5 := by simp
example : 2 + 9 ≠ 9 := by simp
example : 4 ^ 25 < 3 ^ 39 := by norm_num

