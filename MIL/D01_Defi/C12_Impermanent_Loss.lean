import MIL.Common
import Std

open Std
open Lean
open Nat
open Array

-- https://www.ledger.com/academy/glossary/impermanent-loss
-- https://medium.com/hashkey-group/the-quantification-and-hedging-of-impermanent-loss-4011bf6a8552
-- https://docs.uniswap.org/contracts/v2/concepts/advanced-topics/understanding-returns
-- https://blog.quillaudits.com/trending/impermanent-losses-explained-part2-defi-in-out



def natArray : Array ℕ    := #[0, 1, 2]
def m : Array ℕ := range 100


-- impermanent-loss = 2 * sqrt(price_ratio) / (1+price_ratio) – 1

#eval m
