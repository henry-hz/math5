import MIL.Common



open Nat


example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl


example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]



-- Use reflexivity to confirm the equality, as they are definitionally the same.
example : 2 = succ (succ 0) := by
  rfl

example : 3 = succ (succ (succ 0)) := by
  rfl



theorem one_eq_succ_zero: 1 = .succ 0 := by rfl
theorem two_eq_succ_one: 2 = .succ 1 := by rfl
theorem three_eq_succ_two: 3 = .succ 2 := by rfl
theorem four_eq_succ_three: 4 = .succ 3 := by rfl

theorem cow : 2 + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rewrite [add_succ]
  rewrite [one_eq_succ_zero]
  rewrite [add_succ, add_zero] -- two rewrites at once
  rewrite [← three_eq_succ_two] -- change `succ 2` to `3`
  rewrite [← four_eq_succ_three]
  rfl

example : 2 = succ (succ 0) := by
  rewrite [two_eq_succ_one]
  rewrite [one_eq_succ_zero]
  rfl

-- if h is a proof of X = Y then rw [h] will turn Xs into Ys. But what if
-- we want to turn Ys into Xs? To tell the rw tactic we want this,
-- we use a left arrow ←. Type \l and then hit the space bar to get this arrow.
example : 2 = succ (succ 0) := by
  rewrite [← one_eq_succ_zero]
  rewrite [← two_eq_succ_one]
  rfl


example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero b]
  rw [add_zero c]


example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [add_zero]

