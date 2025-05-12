import MIL.Common
import Std

open Std
open Lean
open Nat
open Array



def freq    : ℚ := 5/100  -- [%]
def severity: ℚ := 1000   -- [BRL]
def premium : ℚ := 200    -- [BRL]
def group   : ℚ := 20     -- [people]
def fee     : ℚ := 2/100  -- [%]
def payout  : ℚ := freq * group * severity

#check payout
#eval payout
