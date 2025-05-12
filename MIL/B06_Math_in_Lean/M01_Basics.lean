import MIL.Common
import Std

open Std
open Lean
open Nat

-- mapsto ↦
-- https://leanprover-community.github.io/mathematics_in_lean/C01_Introduction.html#getting-started

#check 2 + 2

def ferm := ∀ x y z n : ℕ, n > 2 ∧ x * y * z != 0 → x ^ n + y ^ n != z ^ n

#check ferm

theorem easy : 2 + 2 = 4 := by
  rfl

#check easy

theorem hard : ferm := by
  sorry

#check hard



-- 4 ways of writing

example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩


example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩ -- m n natural, assume n = 2 * k
  use m * k          -- prove m*n = twice m*k
  rw [hk]
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]


#check mul_add
