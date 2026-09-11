import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O02e, THE CYCLIC GAP SUM IS 2π

THE HEADLINE OF O2.  With the standard wrap convention `a m = a 0 + 2π`, the consecutive
gaps of a cyclically-ordered family of arguments telescope to `2π` exactly.

The campaign report scoped this at 300-600 lines as a missing Mathlib theory.  It is
`Finset.sum_range_sub` -- Mathlib HAS the telescope.  What O2 actually costs is the
ENUMERATION plumbing (O02_SCAFFOLD), not this identity.

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

theorem o02e_cyclic_gap_sum (m : ℕ) (a : ℕ → ℝ) (hwrap : a m = a 0 + 2 * Real.pi) :
    ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi := by
  rw [Finset.sum_range_sub a m, hwrap]
  ring
