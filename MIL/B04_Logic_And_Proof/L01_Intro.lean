import MIL.Common
import Std

open Std
open Lean
open Nat

-- sqrt(2) is irrational, can not be expressed as a fraction

-- https://github.com/leanprover-community/mathlib4/wiki/Lean-4-survival-guide-for-Lean-3-users

section



variable (A H S D B: Prop)
-- https://leanprover.github.io/logic_and_proof/propositional_logic.html#a-puzzle

-- assume h : P ∧ Q,: This line starts the proof by assuming that the hypothesis h is P ∧ Q.
-- This is the starting point of the proof.
-- have P, from and.left h,: This line introduces a new fact into the proof context. It uses
-- the and.left function to extract the first component of the conjunction h, which is P.
-- This is a way to "have" P as a fact in the proof context.
-- have Q, from and.right h,: Similarly, this line introduces Q as a fact in the proof context
-- by extracting the second component of the conjunction h using the and.right function.
-- show Q ∧ P, from and.intro ‹Q› ‹P›: This line concludes the proof by showing that Q ∧ P is true.
-- It uses the and.intro function to construct a conjunction from Q and P. The ‹...› syntax is used
-- to refer to the facts Q and P that were introduced earlier.

-- https://stackoverflow.com/questions/75055993/assume-in-lean-4
-- https://terrytao.wordpress.com/2023/12/05/a-slightly-longer-lean-4-proof-tour/
theorem WetTheorem :
forall Rain Hydrant Wet: Prop,
    (Rain ∨ Hydrant) → -- raining or hydrant on;
    (Rain → Wet) →     -- if raining then wet;
    (Hydrant → Wet) →  -- if hydrant on then wet;
    Wet                -- then wet
:= by
-- setup
  intro Rain Hydrant Wet
  intro (RainingOrHydrantRunning : (Rain ∨ Hydrant))
  intro (RainMakesWet: (Rain → Wet))
  intro (HydrantMakesWet: (Hydrant → Wet))
-- the core of the proof
  cases RainingOrHydrantRunning
  case inl raining =>
    exact RainMakesWet raining
  case inr running =>
    exact HydrantMakesWet running

variable (P Q: Prop)

section
variables (P Q : Prop)

theorem my_t: P ∧ Q → Q ∧ P := by
  intro h : P ∧ Q

theorem my_theorem : P ∧ Q → Q ∧ P := by
intro h = P ∧ Q
have P, from and.left h
have Q, from and.right h
show Q ∧ P, from and.intro ‹Q› ‹P›
