import MIL.Common
import Std

open Std
open Lean
open Nat

-- https://lean-lang.org/lean4/doc/

-- What is Lean

def greet (name: String) := s!"Hi {name}"
def gree2 (tel: ℕ) := s!"Hi {tel}"
def gree3 (num: ℤ)  := s!"Hey {num}"

#eval greet "jim"
#eval gree2 23
#eval gree3 23
#eval greet "jay"

-- functor examples
-- learn well functor and applicatives before getting deep into monads!
#eval [1,2,3].map (λ x => toString x)
#eval ["jim", "h", "ow"].map (λ x => x.length)

inductive Palindrome (α : Type) : List α → Prop where
  | nil       : Palindrome []
  | single    : (a : α)
  | sandwich  : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])


-- https://lean-lang.org/lean4/doc/tour.html

-- BASIC FUNCTIONS
namespace BasicFunctions
#eval 3 + 3

def sf x := x + 3
#eval sf 3

def sf2 (a: ℕ ) (b: ℕ):= a + b
def sf3 := sf2 3 -- partial application
#eval sf2 3 3
#eval sf3 9
#eval println! "hey {sf3 3}"
#eval println! "hsdf {sf2 2 3}"
#eval println! "hey {[1,2,3].map (λ x => toString x)}"

end BasicFunctions
