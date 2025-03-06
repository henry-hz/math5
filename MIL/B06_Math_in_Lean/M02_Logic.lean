import MIL.Common
import Std


open Std
open Lean
open Nat


-- for every real number x, if x is bigger or equal zero
-- the the absolute value of x is equals x.

#check ∀ x : ℝ, 0 ≤ x → |x| = x

-- logical implication
axiom p : Prop
axiom q : Prop

#check p → q
#check p ∧ q
#check ∀ (a : p), a ∨ q
#check Π (a : p), q
#check (a : p) → q
theorem ex1 (a : p) : q := sorry
#print ex1


-- function types
axiom A : Type
axiom B : Type
#check A → B
#check ∀ (a : A), B
#check Π (a : A), B
#check (a : A) → B
def ex2 (a : A) : B := sorry
#print ex2

-- forall
axiom r : A -> Prop
#check ∀ (x : A), r x
#check Π (x : A), r x
#check (x : A) → r x
theorem ex3 (x : A) : r x := sorry
#print ex3

-- dependent function types
axiom C : A -> Type
#check ∀ (x : A), C x
#check Π (x : A), C x
#check (x : A) → C x
def ex4 (x : A) : C x := sorry
#print ex4

-- this code is checking a proposition that states: for all real numbers x, y,
-- and ε, if ε is greater than 0 and less than or equal to 1, and if the
-- absolute value of x is less than ε and the absolute value of y is less
-- than ε, then the absolute value of the product of x and y is also less
-- than ε. This proposition is essentially stating a condition for the
-- product of two real numbers to be close to zero when both numbers are close to zero.
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε


-- https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html


