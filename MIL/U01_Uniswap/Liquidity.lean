import MIL.Common
import Std

open Std
open Lean
open Float
open Array

-- ============================================================================
-- Uniswap V3: Concentrated Liquidity Math
-- https://uniswapv3book.com/milestone_1/calculating-liquidity.html
-- ============================================================================
--
-- WHAT IS THIS FILE ABOUT?
-- ========================
-- Uniswap is a decentralized exchange (DEX) where people swap tokens (e.g. ETH ↔ USDC).
-- Liquidity providers (LPs) deposit pairs of tokens so others can trade against them.
--
-- In Uniswap V3, LPs don't spread their money across ALL possible prices.
-- Instead, they pick a price RANGE (e.g. "I think ETH will stay between $4545 and $5500").
-- This is called "concentrated liquidity" — your capital works harder in a smaller zone.
--
-- The scenario here:
--   • Token pair: ETH / USDC
--   • Current price: 1 ETH = 5000 USDC
--   • LP's chosen range: 4545 to 5500 USDC per ETH
--   • LP deposits: 1 ETH + 5000 USDC
--
-- The code below computes how much "liquidity" (L) these deposits represent,
-- and verifies the token amounts are consistent.
--
-- KEY INSIGHT: Uniswap V3 works with √price (square root of price) instead of
-- price directly. This makes the core math simpler — most formulas become linear
-- in √price instead of involving fractions-of-fractions.
-- ============================================================================


def natArray : Array ℕ    := #[0, 1, 2]
def m : Array ℕ := range 100


-- ============================================================================
-- TICKS
-- ============================================================================
-- A "tick" is just an integer index for a price level.
-- Uniswap doesn't store prices as decimals. Instead it uses:
--
--     price = 1.0001 ^ tick
--
-- Each tick is a 0.01% (1 basis point) step in price.
-- Tick 0 = price 1.0, tick 1 = price 1.0001, tick -1 = price 0.9999, etc.
--
-- To go backwards (price → tick), we take the log base 1.0001:
--
--     tick = floor( log(price) / log(1.0001) )
--
-- The floor() is needed because ticks must be whole numbers.
--
-- 📊 DESMOS: To visualize the price↔tick relationship, go to desmos.com/calculator and type:
--   Line 1: y = 1.0001^x          (this plots price as a function of tick)
--   Line 2: y = \frac{\ln(x)}{\ln(1.0001)}   (this plots tick as a function of price)
--   You'll see an exponential curve (line 1) and a logarithmic curve (line 2).
--   They are inverses of each other — reflecting across y = x.
--   Try clicking on line 2 and restricting the domain: y = \frac{\ln(x)}{\ln(1.0001)} {4000 < x < 6000}
--   to zoom into the price range relevant to this example.
-- ============================================================================
/- example: ln(a^b) := bln(a) -/


noncomputable def iC := Real.log (Real.sqrt 1.0001) * 70.71

def i2 := log (sqrt 1.0001) * 70.71
#eval i2

-- floor is necessary because ticks are integers
def price_to_tick (p : Float) : Float :=
  floor (log p / log 1.0001)

#eval price_to_tick 5000   -- ≈ 85176
#eval price_to_tick 4545   -- ≈ 84222
#eval price_to_tick 5500   -- ≈ 86129


-- ============================================================================
-- Q96 FIXED-POINT SCALING
-- ============================================================================
-- Blockchains (EVM) can't do floating-point math. So Uniswap stores √price as
-- a "fixed-point" integer: multiply the real value by 2^96, then store as an integer.
--
-- This is called Q64.96 notation: 64 bits for the integer part, 96 bits for decimals.
-- q96 = 2^96 ≈ 7.92 × 10^28
--
-- In this code, all "sqrtp" values are √price × q96.
-- Whenever you see "/ q96" or "* q96" it's just converting between the
-- scaled (on-chain) representation and the real math value.
--
-- Think of q96 as a unit conversion factor — like multiplying by 100 to turn
-- dollars into cents. It doesn't change the math, just shifts the decimal.
-- ============================================================================

def q96 : Float := Float.ofNat (2 ^ 96)

#eval q96


-- ============================================================================
-- SQRT PRICE
-- ============================================================================
-- price_to_sqrtp: takes a human-readable price (like 5000) and returns √price × q96.
--
--     sqrtp = √price × 2^96
--
-- Why square root? Because the Uniswap V3 AMM curve is:
--     (x + L/√P_b) × (y + L·√P_a) = L²
-- where x = token0 amount, y = token1 amount, L = liquidity.
-- Using √price makes the derivatives (how much y you get per x) linear.
--
-- 📊 DESMOS: To see how √price relates to price:
--   Line 1: y = \sqrt{x}          (√price as a function of price)
--   Restrict to our range: y = \sqrt{x} {4545 ≤ x ≤ 5500}
--   Add points for our three key prices:
--   Line 2: (4545, \sqrt{4545})
--   Line 3: (5000, \sqrt{5000})
--   Line 4: (5500, \sqrt{5500})
-- ============================================================================

def price_to_sqrtp (p : Float) : Float :=
  Float.sqrt p * q96

def sqrtpLow : Float := price_to_sqrtp 4545.0   -- √4545 × q96
def sqrtpCur : Float := price_to_sqrtp 5000.0   -- √5000 × q96
def sqrtpUpp : Float := price_to_sqrtp 5500.0   -- √5500 × q96

#eval sqrtpLow


-- Helper: ensures pa ≤ pb (lower sqrt-price first).
def order_pair (pa pb: Float) : Float × Float :=
  if pa > pb then (pb, pa) else (pa, pb)


-- ============================================================================
-- LIQUIDITY FROM TOKEN AMOUNTS
-- ============================================================================
-- "Liquidity" (L) is a single number that measures how deep your position is.
-- Higher L = more tokens available for swaps = less price impact per trade.
--
-- There are TWO formulas because each token constrains L differently:
--
-- ── liquidity0: how much L can we get from our token0 (ETH) deposit? ──
--
--   Pure math (no q96 scaling):
--     L = Δx × √Pa × √Pb / (√Pb − √Pa)
--
--   where:
--     Δx  = amount of token0 deposited (e.g. 1 ETH)
--     √Pa = √(lower price of the range where token0 is active)
--     √Pb = √(upper price of the range where token0 is active)
--
--   Intuition: if √Pb − √Pa is small (narrow range), the same Δx gives MORE liquidity.
--   Your capital is concentrated, so it provides more depth per unit.
--
--   In code, pa and pb are already scaled by q96, so we divide by q96 once
--   to cancel one factor: (amount * pa * pb / q96) / (pb - pa)
--
-- ── liquidity1: how much L can we get from our token1 (USDC) deposit? ──
--
--   Pure math:
--     L = Δy / (√Pb − √Pa)
--
--   where:
--     Δy  = amount of token1 deposited (e.g. 5000 USDC)
--     √Pb, √Pa = sqrt-prices bounding the range where token1 is active
--
--   Even simpler: your USDC is spread evenly across the √price range.
--
--   In code, pa/pb are scaled by q96, so we multiply amount by q96:
--   amount * q96 / (pb - pa)
--
-- 📊 DESMOS: To see how liquidity changes with range width:
--   (Using simplified numbers — pretend √Pa ≈ 67.4, √Pb ≈ 74.2 for our range)
--
--   Line 1: L_x(b) = \frac{1 \cdot 67.4 \cdot b}{b - 67.4}    (L from 1 ETH, varying upper √price b)
--     This shows: as b → 67.4 (range shrinks to zero), L → ∞. Narrower range = more liquidity.
--     Restrict domain: L_x(b) = \frac{1 \cdot 67.4 \cdot b}{b - 67.4} {68 ≤ b ≤ 100}
--
--   Line 2: L_y(b) = \frac{5000}{b - 67.4}                      (L from 5000 USDC)
--     Restrict: L_y(b) = \frac{5000}{b - 67.4} {68 ≤ b ≤ 100}
--
--   Both curves are hyperbolas — liquidity explodes as the range narrows.
-- ============================================================================

def liquidity0 (amount pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  (amount * (pa * pb) / q96) / (pb - pa)

def liquidity1 (amount pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  amount * q96 / (pb - pa)


-- ============================================================================
-- TOKEN AMOUNTS FROM LIQUIDITY
-- ============================================================================
-- These are the inverse formulas: given a liquidity value L and a price range,
-- how many tokens does the position hold?
--
-- ── calc_amount0: token0 (ETH) amount ──
--
--   Pure math:
--     Δx = L × (√Pb − √Pa) / (√Pa × √Pb)
--
--   which is the same as:
--     Δx = L × (1/√Pa − 1/√Pb)
--
--   Intuition: token0 amount depends on the difference of RECIPROCAL sqrt-prices.
--   When price goes UP (more USDC per ETH), your ETH balance goes DOWN.
--
-- ── calc_amount1: token1 (USDC) amount ──
--
--   Pure math:
--     Δy = L × (√Pb − √Pa)
--
--   Intuition: token1 amount is simply liquidity × the width of the √price range.
--   When price goes DOWN, your USDC balance goes DOWN.
--
-- 📊 DESMOS: To see how token amounts change as price moves within the range:
--   Let L = 1000 (arbitrary), √Pa = 67.4 (lower), √Pb = 74.2 (upper).
--   Let p = current √price (slider).
--
--   Line 1: Add a slider: a = 67.4 (rename to √Pa)
--   Line 2: Add a slider: b = 74.2 (rename to √Pb)
--   Line 3: Add a slider: L = 1000
--   Line 4: Add a slider: p = 70.7 (current √price, with min=a, max=b)
--   Line 5: x(p) = L \cdot \frac{b - p}{p \cdot b}        (ETH held at √price p)
--   Line 6: y(p) = L \cdot (p - a)                          (USDC held at √price p)
--
--   Drag the p slider and watch: as price rises, ETH drops and USDC rises.
--   At p = b (upper bound), ETH = 0 (all converted to USDC).
--   At p = a (lower bound), USDC = 0 (all converted to ETH).
-- ============================================================================

def calc_amount0 (liq pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  liq * q96 * (pb - pa) / pa / pb

def calc_amount1 (liq pa pb : Float) : Float :=
  let (pa, pb) := order_pair pa pb
  liq * (pb - pa) / q96


-- ============================================================================
-- PUTTING IT ALL TOGETHER
-- ============================================================================
-- eth: 1 ETH expressed in wei (smallest unit, like cents for dollars). 1 ETH = 10^18 wei.
-- amountEth: the LP deposits 1 ETH
-- amountUsdc: the LP deposits 5000 USDC (also in 10^18 base units)
--
-- liq0: liquidity implied by the ETH deposit (between current price and upper bound)
-- liq1: liquidity implied by the USDC deposit (between lower bound and current price)
-- liq:  the MINIMUM of liq0 and liq1. We must take the min because both tokens
--       need to be sufficient. If one gives more L than the other, the excess is unused.
--
-- amount0, amount1: given the final liquidity L, how much ETH and USDC are actually used?
-- These should be ≤ the deposited amounts (1 ETH, 5000 USDC).
--
-- 📊 DESMOS: To visualize the Uniswap V3 AMM curve (the "virtual reserves" curve):
--   This is the fundamental curve that governs swaps within a position's range.
--
--   Line 1: Add slider: L = 1000
--   Line 2: Add slider: a = 67.4     (√P_lower)
--   Line 3: Add slider: b = 74.2     (√P_upper)
--   Line 4: Plot the implicit curve:
--     (x + \frac{L}{b})(y + L \cdot a) = L^2
--
--   This is a shifted hyperbola (like xy = k, but shifted so it intersects the axes).
--   The x-axis is token0 (ETH), y-axis is token1 (USDC).
--   The curve only applies within the range — outside it, the position is fully
--   in one token and no longer participates in swaps.
--
--   To see the classic xy = k for comparison, add:
--   Line 5: x \cdot y = L^2          (the Uniswap V2 curve — unbounded, less capital efficient)
-- ============================================================================

def eth : Float := Float.ofNat (10 ^ 18)
def amountEth : Float := 1.0 * eth
def amountUsdc : Float := 5000.0 * eth

def liq0 : Float := liquidity0 amountEth sqrtpCur sqrtpUpp
def liq1 : Float := liquidity1 amountUsdc sqrtpCur sqrtpLow
def liq  : Float := Float.floor (min liq0 liq1)

def amount0 : Float := Float.floor (calc_amount0 liq sqrtpUpp sqrtpCur)
def amount1 : Float := Float.floor (calc_amount1 liq sqrtpLow sqrtpCur)

#eval sqrtpLow
#eval sqrtpCur
#eval sqrtpUpp

#eval liq0
#eval liq1
#eval liq

#eval amount0
#eval amount1
#eval (amount0, amount1)
