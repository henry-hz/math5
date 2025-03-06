import MIL.Common
import Std

open Std
open Lean
open Nat

--- https://hrmacbeth.github.io/math2001/index.html)

-- a and b are rational
-- supose  a - b = 4 and ab = 1
-- show that (a + b)^2 = 20


example : 1 + 2 = 3 := rfl
example : 3 * 23 = 23 * 3 := by rfl
example : 5 * 2  = sqrt 100 := by rfl
example (x y : ℕ ) : ℕ := x + y

example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring

-- r and s are real, r + 2s = -1 and s = 3. prove r = -7

example (r s : ℝ) (h1: r + 2 * s = -1) (h2: s = 3) : r = -7  :=
  calc
  r = r + 2 * s - 2 * s := by ring
  _ = -1 - 2 * s        := by rw [h1]
  _ = -1 - 2 * 3        := by rw [h2]
  _ = -7                := by ring



example {a b m n : ℤ}
        (h1: a * m + b * n = 1)
        (h2: b ^ 2 = 2 * a ^ 2) :
        (2 * a * n + b * m) ^ 2 = 2 :=
          calc
        (2 * a * n + b * m) ^ 2
           = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
         _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw[h1,h2]
         _ = 2 := by ring


-- let a,b,c,d,f be integers
-- ad = bc
-- cf = de
-- show d(af - be) = 0

example {a b c d e f : ℤ} (h1: a*d = b*c) (h2: c*f = d*e) : d*(a*f - b*e) = 0 :=
calc
  d*(a*f - b*e) = d*(a*f) - d*(b*e)   := by ring
              _ = d*(a*f) - d*(b*e)   := by ring
              _ = d*a*f   - d*b*e     := by ring
              _ = a*d*f   - d*e*b     := by ring
              _ = b*c*f   - c*f*b     := by rw[h1,h2]
              _ = b*c*f   - b*c*f     := by ring
              _ = 0                   := by ring

-- as the solution is already the goal, we add/sub 4
-- on the first step
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
calc
  x = (x + 4) - 4 := by ring
  _ = 2 - 4       := by rw[h1]
  _ = -2          := by ring


-- 1.3.1
example {a b : ℤ} (h1: a = 2*b + 5) (h2: b = 3) : a = 11 :=
calc
  a = 2*b + 5 := by rw[h1]
  _ = 2*3 + 5 := by rw[h2]
  _ = 11      := by ring



example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
calc
  x = (x + 4) - 4 := by ring
  _ = (2)  - 4    := by rw[h1]
  _ = -2          := by ring



-- 1.3.3
/-
This proof demonstrates the step-by-step calculation to prove that a = 9 given
two hypotheses:
h1: a - 5*b = 4
h2: b + 2 = 3

1. a = a
   This is the starting point, asserting that a is equal to itself.
2. _ = a - 5*b + 5*b
   We add and subtract 5*b, which doesn't change the value (ring property).
3. _ = 4 + 5*b
   We replace (a - 5*b) with 4 using hypothesis h1.
4. _ = -6 + 5 * (b + 2)
   We rewrite 4 as (-6 + 10) and factor out 5 from 5*b + 10.
5. _ = -6 + 5 * 3
   We replace (b + 2) with 3 using hypothesis h2.
6. _ = -6 + 15
   We multiply 5 * 3.
7. _ = 9
   We perform the final addition to get the result.

Each step uses either ring (for algebraic manipulations) or rw (for rewriting
using hypotheses) to justify the transformation.
-/
example {a b : ℝ} (h1: a - 5*b = 4) (h2: b + 2 = 3) : a = 9 :=
calc
  a = a                   := by ring
  _ = a - 5*b + 5*b       := by ring
  _ = 4 + 5*b             := by rw[h1]
  _ = -6 + 5 * (b + 2)    := by ring    -- we extracted the 4 with -6+10
  _ = -6 + 5 * 3          := by rw[h2]
  _ = -6 + 15             := by ring
  _ = 9                   := by ring




-- 1.3.4
-- https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#proving-equalities
-- we use the Brahmagupta's identity as the second step

variable {R : Type*} [CommRing R]
{a b x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n : ℝ}

-- Brahmagupta's identity in one step
theorem sq_add_mul_sq_mul_sq_add_mul_sq :
    (x₁ ^ 2 + n * x₂ ^ 2) * (y₁ ^ 2 + n * y₂ ^ 2) =
    (x₁ * y₁ - n * x₂ * y₂) ^ 2 + n * (x₁ * y₂ + x₂ * y₁) ^ 2 := by ring


-- Brahmagupta's identity with all algebraic steps
theorem sq_add_mul_sq_mul_sq_add_mul_sq2 (x₁ x₂ y₁ y₂ n : ℤ) :
    (x₁ ^ 2 + n * x₂ ^ 2) * (y₁ ^ 2 + n * y₂ ^ 2) =
    (x₁ * y₁ - n * x₂ * y₂) ^ 2 + n * (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  have lhs : (x₁ ^ 2 + n * x₂ ^ 2) * (y₁ ^ 2 + n * y₂ ^ 2) =              -- expand left
    x₁^2 * y₁^2 + n * x₁^2 * y₂^2 + n * x₂^2 * y₁^2 + n^2 * x₂^2 * y₂^2 := by ring
  have rhs : (x₁ * y₁ - n * x₂ * y₂) ^ 2 + n * (x₁ * y₂ + x₂ * y₁) ^ 2 =  -- expand right
    (x₁ * y₁)^2 + n^2 * (x₂ * y₂)^2 - 2*n * x₁ * y₁ * x₂ * y₂ +
    n * (x₁ * y₂)^2 + n * (x₂ * y₁)^2 + 2*n * x₁ * y₂ * x₂ * y₁ := by ring
  have rhs_simplified :
    (x₁ * y₁)^2 + n^2 * (x₂ * y₂)^2 - 2*n * x₁ * y₁ * x₂ * y₂ +
    n * (x₁ * y₂)^2 + n * (x₂ * y₁)^2 + 2*n * x₁ * y₂ * x₂ * y₁ =
    x₁^2 * y₁^2 + n * x₁^2 * y₂^2 + n * x₂^2 * y₁^2 + n^2 * x₂^2 * y₂^2 := by ring
  calc                                                                    -- prove equality
    (x₁ ^ 2 + n * x₂ ^ 2) * (y₁ ^ 2 + n * y₂ ^ 2)
      = x₁^2 * y₁^2 + n * x₁^2 * y₂^2 + n * x₂^2 * y₁^2 + n^2 * x₂^2 * y₂^2 := lhs
    _ = (x₁ * y₁)^2 + n^2 * (x₂ * y₂)^2 - 2*n * x₁ * y₁ * x₂ * y₂ +
        n * (x₁ * y₂)^2 + n * (x₂ * y₁)^2 + 2*n * x₁ * y₂ * x₂ * y₁ := by rw [←rhs_simplified]
    _ = (x₁ * y₁ - n * x₂ * y₂) ^ 2 + n * (x₁ * y₂ + x₂ * y₁) ^ 2   := by rw [←rhs]


example {a b m n : ℝ} (h1: b^2        = 2*a^2)
                      (h2: a*m + b*n  = 1) :
                      (2*a*n + b*m)^2 = 2  :=
calc
  (2*a*n + b*m)^2 = (2*a*n + b*m)^2                       := by ring
  (2*a*n + b*m)^2 = (2*a*n)^2 + 2*(2*a*n)*(b*m) + (b*m)^2 := by ring
