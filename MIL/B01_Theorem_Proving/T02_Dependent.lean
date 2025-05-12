import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common
import Std

namespace B01_dep
open Std
open Lean
open Nat

-- Type Theory: every expression has a type

def m: ℕ := 1
#check m

def n: ℕ := 0
#check n
#check m * n
#check true ∨ false
#check ℕ × ℕ
#check (3,2).1
#eval (3,2).1


-- Types as objects: types are first class citzens

#check ℕ
#check ℕ → (ℕ → ℕ)

def α : Type := ℕ
#check α
#check Nat
#check Nat → Nat
#check ℕ → (ℕ → ℕ)


def β : Type := Bool
#check β
def a1 : β := true
def a2 : β := false
#check a1
#check Prod ℕ ℕ


section a3

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice

end a3

#print compose

#check Type
#check Type 1
#check List
#check Type 0
universe u

def F (α : Type u) : Type u := Prod α α

universe u1
def F1 (α : Type u) : Type u := Prod α α
#check F1

-- avoiding unniverse
-- def F2.{u3} (α : Type u) : Type u := Prod α α

-- declare 3 types, alpha, beta and gamma, a function g that receives beta and returns gamma
-- a function f that receives alpha and returns beta, declare that x is a value of type
-- alpha and the function composition g (f x) is the body of the function.
-- It applies f to x, then applies g to the result.
section a4

#check fun (α β γ : Type) (g: β → γ) (f: α → β) (x : α) => g (f x)
def f := fun x: ℕ => x
#eval f 3
#check (fun x: ℕ => x) 9


section definitions
-- continue: https://leanprover.github.io/theorem_proving_in_lean4/dependent_type_theory.html#what-makes-dependent-type-theory-dependent

def double (x : ℕ) : ℕ := x + x
#eval double 3

def double₂ : ℕ → ℕ := fun x => x + x
#eval double₂ 3

def double₃ : ℕ → ℕ := fun x => x + x
#eval double₃ 9

-- https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_A/section02reals/reals.html
def double₄ : ℝ → ℝ := fun y => y + y

theorem double₄_works_with_reals (x : ℝ) : ∃ y : ℝ, double₄ x = y := by
  use x + x
  rfl


#check double₄_works_with_reals
#eval double₄  0.2
