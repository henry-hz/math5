import MIL.Common
import Std

open Std
open Lean
open Nat
open Array


def WAD : ℕ := 10 ^ 18
def RAY : ℕ := 10 ^ 27

def deposit : ℚ := 10.0
#eval deposit / 0.02
#eval 10 / 0.021
def dep1 : ℚ := 10/0.021
#eval dep1 * 0.021
def dep2 :=  10 / 0.029
#eval dep2 *0.031
