import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common
import Std

namespace B01_dep
open Std
open Lean
open Nat


-- Propositions as Types: we need an assertion and proof language, so dependent
-- type theory is used also to build this language.

#check And
#check Or
#check true ∨ false
#check Implies

variable (p q r : Prop)

#check p
#check And p q
#check p ∧ q
#check Or p q
#check Implies (And p q) (And q p)


def Implies (p q : Prop) : Prop := p → q

structure P2 (p: Prop) : Type where
  p2 : p

structure Proof (p : Prop) : Type where
  proof : p
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

-- https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html
