import Mathlib.Data.Real.Basic
import MIL.Common
import Std

open Std
open Lean
open Nat
open Array


def WAD : ℕ := 10 ^ 18
def RAY : ℕ := 10 ^ 27

def a : ℕ := 2
def b : ℕ := 1000

def c : ℕ := a * WAD/ b

#eval c
#eval c * 7
#eval c / 7
def z := c + (9*WAD)
def z1 := (z * c) / WAD
#eval z1



def d : ℕ := (c * 7)


#eval a*WAD/b


#eval WAD
