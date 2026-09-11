import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O02f, SIX GAPS FIT IN A CIRCLE AND NO MORE

If the `m` consecutive cyclic gaps are each at least `π / 3` and they sum to `2π`, then
`m ≤ 6`.  This is the counting half of "an interior vertex has unit-degree at most 6",
kept separate from any geometry so that it is pure arithmetic over ℝ.

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

theorem o02f_gap_bound_card_le_six (m : ℕ) (a : ℕ → ℝ)
    (hwrap : a m = a 0 + 2 * Real.pi)
    (hgap : ∀ i, i < m → Real.pi / 3 ≤ a (i + 1) - a i) :
    m ≤ 6 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsum : ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi := by
    rw [Finset.sum_range_sub a m, hwrap]
    ring
  have hlow : ∑ _i ∈ Finset.range m, (Real.pi / 3)
      ≤ ∑ i ∈ Finset.range m, (a (i + 1) - a i) :=
    Finset.sum_le_sum fun i hi => hgap i (Finset.mem_range.mp hi)
  rw [Finset.sum_const, Finset.card_range, hsum] at hlow
  first
    | rw [nsmul_eq_mul] at hlow
    | simp only [nsmul_eq_mul] at hlow
  have hm : (m : ℝ) ≤ 6 := by
    by_contra hc
    push_neg at hc
    nlinarith [hlow, hpi, hc]
  exact_mod_cast hm
