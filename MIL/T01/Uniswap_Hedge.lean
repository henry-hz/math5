import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import MIL.Common
import Std

open Std
open Lean
open Nat



namespace algo_1

-- https://www.techiedelight.com/find-pair-with-given-sum-array/

def my_list : List ℕ := [1,2,3,4]
#eval my_list


def my_2 := my_list ++ [5,6]
#eval my_2
#eval my_2.length




def myList : List Nat := [1, 2, 3, 4, 5]
def squaredList := myList.map (fun x => x * x) -- Squares each element

def evenList := myList.filter (fun x => x % 2 == 0) -- Keeps only even numbers


#eval evenList


def sumit : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sumit xs


def a := sumit [1,3,4,9,234]
#eval a
