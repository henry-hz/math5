import MIL.Common


example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl


example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]
  rfl


