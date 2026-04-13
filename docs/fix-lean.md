# Fix Log: Lean Project Build Issues

This document records the issues encountered and the fixes applied to restore the build process for the repository.

## 1. Toolchain Version Mismatch

**Issue:**
The `make deps` command failed with compilation errors in dependencies (`Cache.Lean`, `Batteries.Data.String.Basic`). This was caused by a mismatch between the Lean toolchain version defined in `lean-toolchain` (`v4.29.0-rc1`) and the pinned `mathlib` version in `lakefile.toml` (`v4.21.0`).

**Fix:**
Downgraded the toolchain version to match the dependency.
- **File:** `lean-toolchain`
- **Change:** Updated content from `leanprover/lean4:v4.29.0-rc1` to `leanprover/lean4:v4.21.0`.

## 2. Missing File / Incorrect Path

**Issue:**
`lake build` failed with `error: no such file or directory` for `MIL/T01/Uniswap_Hedge.lean`. The file structure did not match the import path in `MIL.lean` (`import MIL.T01.Uniswap_Hedge`).

**Fix:**
Renamed the directory and file to align with the module path.
- **Old Path:** `MIL/T01_Uniswap_Hedge/Arrays.lean`
- **New Path:** `MIL/T01/Uniswap_Hedge.lean`

## 3. Mathlib Import Adjustments

**Issue:**
Several files in `MIL/HelpersLib` failed to compile due to changes in the Mathlib directory structure and removed tactics.

**Fixes:**
- **File:** `MIL/HelpersLib/Finsupp2.lean`
  - Removed unused import `Mathlib.Tactic.LibrarySearch`.
- **File:** `MIL/HelpersLib/NNReal.lean`
  - Changed `import Mathlib.Data.Real.NNReal` to `import Mathlib.Data.NNReal.Basic`.
- **File:** `MIL/HelpersLib/PReal/Basic.lean`
  - Changed `import Mathlib.Data.Real.NNReal` to `import Mathlib.Data.NNReal.Basic`.

## 4. Internal Import Path Corrections

**Issue:**
Files within `MIL/HelpersLib` were using incorrect relative or shortened import paths (e.g., `import HelpersLib...`) which could not be resolved.

**Fixes:**
Updated imports to use the full `MIL` namespace.
- **File:** `MIL/HelpersLib/NNReal.lean`
  - `import HelpersLib.PReal.Basic` -> `import MIL.HelpersLib.PReal.Basic`
- **File:** `MIL/HelpersLib/PReal/Order.lean` & `MIL/HelpersLib/PReal/Subtraction.lean`
  - `import HelpersLib.PReal.Basic` -> `import MIL.HelpersLib.PReal.Basic`
  - `import HelpersLib.PReal.Subtraction` -> `import MIL.HelpersLib.PReal.Subtraction`
- **File:** `MIL/HelpersLib/Finsupp2.lean`
  - `import HelpersLib.Prod` -> `import MIL.HelpersLib.Prod`

## 5. Code Deprecations and Errors in HelpersLib

**Issue:**
The upgrade/downgrade exposed deprecated functions, missing instances, and removed lemmas in `MIL/HelpersLib`.

**Fixes:**
- **File:** `MIL/HelpersLib/PReal/Basic.lean`
  - Replaced `NNReal.coe_eq` with `NNReal.coe_inj` as the former was removed/renamed in the active Mathlib version.
- **File:** `MIL/HelpersLib/Finsupp2.lean`
  - **Duplicate Definitions:** Removed `Finsupp.uncurry_curry` and `Finsupp.uncurry_apply` because they are now declared in Mathlib.
  - **Missing Instances:** Added `[DecidableEq α] [DecidableEq β]` context to `curried_swap` and `curried_swap_def` to satisfy type class synthesis.
  - **Deprecated Function:** Replaced `Finsupp.erase_of_not_mem_support` with `Finsupp.erase_of_notMem_support`.
