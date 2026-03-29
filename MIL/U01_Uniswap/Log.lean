/-
# Educational Proof: log(x ^ y) = y * log(x)

This file is a guided tutorial that proves the logarithm–power rule in
**multiple ways**, explains every tactic, and gives numerical sanity-checks
so the student can see *why* the theorem is true, not just *that* it is true.

## Mathematical background

The **natural logarithm** `log` (base e ≈ 2.718…) is the inverse of the
exponential function `exp`.  Its two defining identities are:

  exp(log x) = x   (for x > 0)
  log(exp x) = x   (for all x)

From these two facts, every other logarithm rule follows—including the
power rule we prove here.

## Notation in Lean / Mathlib

  `Real.log`   — the natural logarithm, extended to all of ℝ by setting
                 `log x = 0` when `x ≤ 0`.
  `Real.exp`   — the exponential function  eˣ.
  `x ^ n`      — natural-number power  (n : ℕ).
  `x ^ (y:ℝ)`  — real-number power `rpow`, defined as `exp(log x · y)`
                 for `x > 0`.

## What we prove

We prove three **variants** of the power rule, one for each exponent type:

| Variant | Statement |
|---------|-----------|
| ℕ-power | `log(x ^ n) = n * log x` |
| ℤ-power | `log(x ^ n) = n * log x` |
| ℝ-power | `log(x ^ y) = y * log x`  (needs `x > 0`) |

For each variant we give **multiple proof strategies**.
-/

import Mathlib

open Real

/-!
## Part 0 — Numerical sanity-checks

Before we prove anything, let's **verify** the rule on concrete numbers
using floating-point arithmetic.  This builds intuition: "the rule really
does hold; now let's see *why*."
-/

section NumericalExamples
/-!
### Example 1:  log(2³) = 3 · log 2

  2³ = 8
  log 8  ≈ 2.0794
  3 · log 2 ≈ 3 × 0.6931 ≈ 2.0794  ✓
-/
#eval do
  let lhs := Float.log 8.0           -- log(2³) = log(8)
  let rhs := 3.0 * Float.log 2.0     -- 3 · log 2
  IO.println s!"log(2^3) = log(8) = {lhs}"
  IO.println s!"3 * log(2)         = {rhs}"
  IO.println s!"Difference         = {(lhs - rhs).abs}"

/-!
### Example 2:  log(10²) = 2 · log 10

  10² = 100
  log 100 ≈ 4.6052
  2 · log 10 ≈ 2 × 2.3026 ≈ 4.6052  ✓
-/
#eval do
  let lhs := Float.log 100.0         -- log(10²) = log(100)
  let rhs := 2.0 * Float.log 10.0    -- 2 · log 10
  IO.println s!"log(10^2) = log(100) = {lhs}"
  IO.println s!"2 * log(10)           = {rhs}"
  IO.println s!"Difference            = {(lhs - rhs).abs}"

/-!
### Example 3:  log(5⁴) = 4 · log 5

  5⁴ = 625
  log 625 ≈ 6.4378
  4 · log 5 ≈ 4 × 1.6094 ≈ 6.4378  ✓
-/
#eval do
  let lhs := Float.log 625.0         -- log(5⁴) = log(625)
  let rhs := 4.0 * Float.log 5.0     -- 4 · log 5
  IO.println s!"log(5^4) = log(625) = {lhs}"
  IO.println s!"4 * log(5)           = {rhs}"
  IO.println s!"Difference           = {(lhs - rhs).abs}"

/-!
### Example 4 (real exponent):  log(3^1.5) = 1.5 · log 3

  3^1.5 = 3 · √3 ≈ 5.1962
  log(5.1962) ≈ 1.6479
  1.5 · log 3 ≈ 1.5 × 1.0986 ≈ 1.6479  ✓
-/
#eval do
  let lhs := Float.log (5.196152422706632)  -- log(3^1.5) ≈ log(5.196…)
  let rhs := 1.5 * Float.log 3.0            -- 1.5 · log 3
  IO.println s!"log(3^1.5) ≈ {lhs}"
  IO.println s!"1.5 * log(3) = {rhs}"
  IO.println s!"Difference   = {(lhs - rhs).abs}"

end NumericalExamples

/-!
=================================================================
## Part 1 — The ℕ-power rule:  log(x ^ n) = n * log x
=================================================================

This is the most elementary version. The exponent `n` is a natural number
(0, 1, 2, 3, …), so `x ^ n` is just repeated multiplication:

  x ^ 0 = 1
  x ^ (n+1) = x · (x ^ n)

### Why is it true?  (Informal argument)

**By induction on n.**

* **Base case (n = 0):**
    log(x⁰) = log 1 = 0 = 0 · log x.  ✓

* **Inductive step (n → n+1):**
    Assume log(xⁿ) = n · log x.  Then
      log(x^(n+1))
        = log(x · xⁿ)           — definition of power
        = log x + log(xⁿ)       — log-of-product rule
        = log x + n · log x     — induction hypothesis
        = (n + 1) · log x       — algebra.  ✓

The key ingredient is the **log-of-product** rule
  `log(a · b) = log a + log b`,
which itself follows from `exp` being a homomorphism:
  `exp(a + b) = exp a · exp b`.
-/

/-!
### Proof Path 1A — Direct call to Mathlib

Mathlib already has this theorem as `Real.log_pow`.
We can prove our version in one line by invoking it.

**Tactic: `exact`**
  `exact e` closes a goal when expression `e` has exactly the right type.
  Think of it as "here is the proof term, QED."
-/
theorem log_pow_path1A (x : ℝ) (n : ℕ) :
    Real.log (x ^ n) = ↑n * Real.log x := by
  exact Real.log_pow x n
  -- `Real.log_pow` is the Mathlib lemma whose type matches our goal
  -- exactly, so `exact` closes the proof immediately.

/-!
### Proof Path 1B — Induction by hand (the educational proof)

We mimic the informal argument above, using the tactic `induction` to
do case analysis on `n`.

**Tactics used:**
  • `induction n with | ...` — structural induction on a natural number.
  • `simp`  — simplification using a built-in set of rewriting rules.
  • `rw [h]` — rewrite the goal using equation `h`.
  • `ring`  — close goals that are pure algebraic identities.
-/
theorem log_pow_path1B (x : ℝ) (n : ℕ) :
    Real.log (x ^ n) = ↑n * Real.log x := by
  /-
  We do induction on `n`:
    Base case  n = 0:  show log(x⁰) = 0 · log x
    Inductive  n → n+1: show log(x^(n+1)) = (n+1) · log x
  -/
  induction n with
  | zero =>
    /-
    Goal: Real.log (x ^ 0) = ↑0 * Real.log x
    `x ^ 0 = 1` and `↑0 * _ = 0`, so both sides simplify to `log 1 = 0`.
    `simp` handles all of these simplifications at once.
    -/
    simp [Real.log_one]
    -- `simp` rewrites x^0 → 1, log 1 → 0, 0 * _ → 0. Done!
  | succ n ih =>
    /-
    ih : Real.log (x ^ n) = ↑n * Real.log x   — induction hypothesis
    Goal: Real.log (x ^ (n + 1)) = ↑(n + 1) * Real.log x

    Step 1: Case-split on whether x = 0 or x ≠ 0.
    -/
    by_cases hx : x = 0
    · -- Subcase x = 0: both sides become log 0 = 0.
      simp [hx]
    · -- Subcase x ≠ 0:
      have hxn : x ^ n ≠ 0 := pow_ne_zero n hx
      -- Now x ≠ 0 and x^n ≠ 0, so we can use log_mul.
      rw [pow_succ]
      -- Goal becomes: log(x^n * x) = (↑n + 1) * log x
      rw [Real.log_mul hxn hx]
      -- Goal becomes: log(x^n) + log x = (↑n + 1) * log x
      rw [ih]
      -- Goal becomes: ↑n * log x + log x = (↑n + 1) * log x
      push_cast
      -- `push_cast` normalizes the ℕ→ℝ coercions through arithmetic.
      ring
      -- `ring` closes the algebraic identity n·a + a = (n+1)·a.

/-!
### Proof Path 1C — Via the exponential inverse (x > 0)

**Idea:** Since `exp` is injective and `log = exp⁻¹`, we can prove
`log(xⁿ) = n · log x` by showing both sides give the same value
after applying `exp`.

**New tactic: `congr`**
  `congr n` reduces a goal of the form `f a₁ … = f b₁ …` to
  subgoals `a₁ = b₁`, etc. (matching on the outermost `n` levels).
-/
theorem log_pow_path1C (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.log (x ^ n) = ↑n * Real.log x := by
  /-
  For x > 0 we use the exp-log inverse.
  Key facts:
    exp(log(a)) = a         for a > 0
    exp(n · t)  = (exp t)ⁿ  — exp converts multiplication to power
  -/
  -- Step 1: Replace the RHS with log(exp(n · log x))
  rw [← Real.log_exp (↑n * Real.log x)]
  -- Goal: log(xⁿ) = log(exp(n · log x))
  -- Step 2: It suffices to show the arguments of log are equal.
  congr 1
  -- Goal: xⁿ = exp(n · log x)
  -- Step 3: exp(n · t) = (exp t)ⁿ
  rw [Real.exp_nat_mul]
  -- Goal: xⁿ = (exp(log x))ⁿ
  -- Step 4: exp(log x) = x  (since x > 0)
  rw [Real.exp_log hx]
  -- Goal: xⁿ = xⁿ.  Done!


/-!
=================================================================
## Part 2 — The ℤ-power rule:  log(x ^ n) = n * log x
=================================================================

When `n : ℤ` (an integer), `x ^ n` extends to negative exponents:
  x ^ (-k) = 1 / (x ^ k).

The rule `log(x^n) = n · log x` still holds (Mathlib: `Real.log_zpow`).

### Why is it true?

It reduces to the ℕ case plus the identity `log(1/a) = −log a`:
  log(x^(−k)) = log(1/x^k) = −log(x^k) = −(k · log x) = (−k) · log x.
-/

/-!
### Proof Path 2A — Direct Mathlib call
-/
theorem log_zpow_path2A (x : ℝ) (n : ℤ) :
    Real.log (x ^ n) = ↑n * Real.log x := by
  exact Real.log_zpow x n

/-!
### Proof Path 2B — Case-split on sign of n

**New tactic: `cases`**
  `cases n with | ofNat k => ... | negSucc k => ...`
  destructs an integer into its two constructors:
    • `Int.ofNat k` — represents the non-negative integer `k`
    • `Int.negSucc k` — represents the negative integer `-(k+1)`

**New tactic: `push_cast`**
  Pushes coercions (ℕ → ℤ → ℝ) through arithmetic operations so that
  `simp` / `ring` can work on a uniform type.
-/
theorem log_zpow_path2B (x : ℝ) (n : ℤ) :
    Real.log (x ^ n) = ↑n * Real.log x := by
  /-
  Every integer is either a natural number or the negation of one.
  We handle the two cases separately.
  -/
  cases n with
  | ofNat k =>
    /-
    n = ↑k where k : ℕ.
    Goal: log(x ^ (↑k : ℤ)) = ↑(↑k : ℤ) * log x
    This is just the ℕ-power rule in disguise.
    -/
    simp [zpow_natCast, Real.log_pow]
    -- `zpow_natCast` rewrites x^(↑k:ℤ) to x^k.
    -- Then `Real.log_pow` finishes.
  | negSucc k =>
    /-
    n = -↑(k+1).
    x ^ (-(k+1)) = (x ^ (k+1))⁻¹.
    We use log(a⁻¹) = -log(a) and the ℕ case.
    -/
    simp [zpow_negSucc, Real.log_inv, Real.log_pow]
    ring

/-!
=================================================================
## Part 3 — The ℝ-power rule:  log(x ^ y) = y * log x  (x > 0)
=================================================================

When the exponent `y` is a **real number**, the power `x ^ y` (written
`rpow x y` in Lean) is *defined* as:

  x ^ y  :=  exp(log x · y)      (for x > 0).

So the proof is essentially **unfolding the definition**:

  log(x ^ y) = log(exp(log x · y)) = log x · y = y · log x.

The hypothesis `x > 0` is essential: without it, `rpow` is defined
to be 0 or handled specially.
-/

/-!
### Proof Path 3A — Direct Mathlib call
-/
theorem log_rpow_path3A {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.log (x ^ y) = y * Real.log x := by
  exact Real.log_rpow hx y

/-!
### Proof Path 3B — Unfold the definition of rpow

**Key idea:**  Since `x^y := exp(log x · y)` for x > 0, we rewrite
using the definition, then apply `log(exp t) = t`.
-/
theorem log_rpow_path3B {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.log (x ^ y) = y * Real.log x := by
  -- Step 1: Unfold x^y to its definition exp(log x · y)
  rw [rpow_def_of_pos hx]
  -- Goal: log(exp(log x * y)) = y * log x

  -- Step 2: Apply the fundamental identity log(exp t) = t
  rw [Real.log_exp]
  -- Goal: log x * y = y * log x

  -- Step 3: Commutativity of multiplication
  ring

/-!
### Proof Path 3C — Via exp-injectivity

**Idea:** Prove `exp(LHS) = exp(RHS)` and use injectivity of `exp`.

**New tactic: `apply`**
  `apply f` matches the conclusion of `f` against the current goal.
  If `f : A → B → C` and the goal is `C`, then `apply f` creates
  subgoals for `A` and `B`.
-/
theorem log_rpow_path3C {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.log (x ^ y) = y * Real.log x := by
  -- It suffices to show exp applied to both sides gives the same result,
  -- because exp is injective.
  apply Real.exp_injective
  -- Goal: exp(log(x^y)) = exp(y * log x)

  -- Since x^y > 0, we have exp(log(x^y)) = x^y.
  have h_pos : (0 : ℝ) < x ^ y := Real.rpow_pos_of_pos hx y
  rw [Real.exp_log h_pos]
  -- Goal: x^y = exp(y * log x)

  -- Unfold the definition of rpow
  rw [rpow_def_of_pos hx]
  -- Goal: exp(log x * y) = exp(y * log x)
  ring_nf
  -- `ring_nf` normalizes both sides of the equality. Done!

/-!
=================================================================
## Part 4 — Summary & Cheat-Sheet
=================================================================

| Theorem         | Lean name          | Key hypothesis |
|-----------------|--------------------|----------------|
| log(xⁿ) = n·log x  (n:ℕ) | `Real.log_pow`  | none |
| log(xⁿ) = n·log x  (n:ℤ) | `Real.log_zpow` | none |
| log(x^y) = y·log x  (y:ℝ) | `Real.log_rpow` | `0 < x` |

### Tactics cheat-sheet

| Tactic   | What it does |
|----------|-------------|
| `exact`  | Supply the exact proof term to close the goal. |
| `rw`     | Rewrite the goal (or a hypothesis) using an equation. |
| `simp`   | Simplify using a database of known lemmas. |
| `ring`   | Close goals that are algebraic identities in a comm ring. |
| `induction n with` | Structural induction on `n`. |
| `by_cases` | Case-split on a decidable proposition. |
| `have`   | Introduce a local sub-goal / helper fact. |
| `congr`  | Reduce `f a = f b` to `a = b`. |
| `push_neg` | Push negations inward (`¬(a > b)` → `a ≤ b`). |
| `push_cast` | Push coercions (ℕ→ℤ→ℝ) through arithmetic. |
| `apply`  | Apply a lemma whose conclusion matches the goal. |
| `ring_nf`| Normalize ring expressions without necessarily closing the goal. |
| `cases`  | Destruct a value into its constructors. |

### Why does the rule hold? (one-paragraph intuition)

The exponential function `exp` converts **addition into multiplication**:
`exp(a + b) = exp(a) · exp(b)`.  Its inverse, `log`, therefore converts
**multiplication into addition**: `log(a · b) = log a + log b`.
Raising to a power is repeated multiplication, so
`log(x · x · … · x) = log x + log x + … + log x = n · log x`.
For real exponents the same idea works through the *definition*
`x^y := exp(y · log x)`, which directly encodes the rule.
-/

