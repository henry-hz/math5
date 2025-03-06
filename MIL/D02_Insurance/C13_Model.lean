import Mathlib.Data.Real.Basic
import MIL.Common
import Std

open Std
open Lean
open Nat
open Array


def premium := 1000
def event : Bool := true
def provision := 10000
def claims := 5          -- number of claims
def payout := 5000 * claims
def net_payment : ℕ := premium - payout


-- take the occurence of the event and returns the payout
-- amount if the event occurs or zero otherwise
def outcome(occurs: Bool) : ℕ :=
  if occurs then payout else 0

-- the difference between the premium paid and the payout
-- received
def net : ℕ := premium - outcome event



-- prove property that if the event occurs, the policyholder
-- receives the payout
example : event → outcome event = payout := by
  rw [outcome]
  rw [if_pos]
  rfl


-- prove the property that if the event does not occur, the
-- policyholder receives no payout
example : ¬ event → outcome event = 0 := by
  intro h
  rw [outcome]
  rw [if_neg]
  rfl

-- prove the net payment is correct based on the event
example (occurs : Bool) : outcome occurs = payout → net = premium - payout := by
  intro h
  rw [net]
  cases occurs


-- prove the
-- the solvency invariant can be defined as a condition that
-- ensures the insurance company remains solvent after considering
-- the provision fund and the total payout for claims. A simple
-- way to express this in Lean is by ensuring that the provision fund
-- is sufficient to cover the total payout.

def solvency : Prop := provision ≥ payout


example : solvency := by
  unfold solvency
  unfold payout
  unfold provision
  unfold claims
  simp
  linarith





