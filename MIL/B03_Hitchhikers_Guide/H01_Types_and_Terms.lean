import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common
import Std

open Std
open Lean
open Nat


namespace HG


-- use opaque to declare types and constants
opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ



#check fun x : ℤ ↦ g (f (g a x)) (g * b)



def sub1 : ℕ → ℕ
  | zero   => zero
  | succ x => x

#eval sub1 1
#eval succ 4
#eval succ 9
#eval sub1 9
#eval succ 9
#eval zero
#eval zero == 0


def isZero : Nat → Bool
  | zero   => true
  | succ x => false

#eval isZero 1

namespace B02
opaque a : ℤ
def add := λ (a: ℤ) => a + 3
#eval add (-9)

def div := λ a => a / 2934
#eval div 3333

def sub3 : ℕ → ℕ
  | 0   => 0
  | x+1 => x

#eval sub3 3
#eval sub3 1

def isZ : ℕ → Bool
  | 0   => true
  | x+1 => false

#eval isZ 0
#eval isZ 9

-- CHAPTER 2 - pag 21


-- inductive type is a type whose values are built by applying
-- special constants called constructors.

-- definitions of natural numbers

inductive Nat : Type where  -- introduce to the world the new type Nat
  | zero : Nat              -- constructor to start from zero
  | succ : Nat → Nat        -- inductive definition

#check  Nat
#print Nat
#print Int

def fib : ℕ → ℕ
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

#eval fib 33
example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl

example : fib 7 = 21 := rfl

def j := fun n : ℕ ↦ n
def j1 := fun n : ℤ ↦ n
def j2 := fun n : ℕ  ↦ n * 3
def j3 := (fun n :ℕ ↦ sqrt (sqrt n)) 10
def j4 := (fun y : ℤ ↦ 1) 923
#eval j4
#eval j 3
#eval j1 33
#eval j2 23
#eval j3

-- definition of arithmetic expressions [pg 22]

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


def eval : (AExp → (String → ℤ) → ℤ)
  | AExp.num n _ => n
  | (AExp.var x) env => env x
  | (AExp.add e1 e2) env => (eval e1 env) + (eval e2 env)
  | (AExp.sub e1 e2) env =>  (eval e1 env) - (eval e2 env)
  | (AExp.mul e1 e2) env =>  (eval e1 env) * (eval e2 env)
  | (AExp.div e1 e2) env => (eval e1 env) / (eval e2 env)
