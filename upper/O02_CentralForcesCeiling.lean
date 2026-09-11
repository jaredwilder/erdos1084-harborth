import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset

/-! # erdos:1084 upper -- THE m <= 3 RESIDUE, CLOSED AS A THEOREM.

`O02_GapCeiling.lean` derives the gap ceiling `<= π` from the O02 floor `>= π/3` whenever
there are at least FOUR gaps, and leaves `m <= 3` open.  This file shows that residue is
NOT a hole in the proof: the ceiling is EQUIVALENT to `hcentral`, so at `m <= 3` a gap
above `π` does not merely defeat the argument, it makes `hcentral` FALSE.

The mechanism is one line of monotonicity: `arccos (cos t) <= t` for `t >= 0`, with STRICT
inequality above `π` because `arccos` never exceeds `π`.  Summing, the central total can
never exceed the gap total, and it reaches it exactly when no gap is above `π`.

CONSEQUENCE, stated flat: at `m = 1` the single gap is `2π > π`, so `hcentral` is
UNSATISFIABLE; at `m = 2` it forces both gaps to be exactly `π`; at `m = 3` it forces all
three gaps `<= π`.  Nothing is missing at `m <= 3` -- the side condition is real.
-/

theorem arccos_cos_le_self (t : ℝ) (h0 : 0 ≤ t) : Real.arccos (Real.cos t) ≤ t := by
  rcases le_or_gt t Real.pi with h | h
  · exact le_of_eq (Real.arccos_cos h0 h)
  · exact le_trans (Real.arccos_le_pi _) h.le

theorem arccos_cos_lt_self (t : ℝ) (h : Real.pi < t) : Real.arccos (Real.cos t) < t :=
  lt_of_le_of_lt (Real.arccos_le_pi _) h

/-- The central total never exceeds the gap total. -/
theorem central_sum_le_gap_sum (m : ℕ) (a : ℕ → ℝ)
    (hnn : ∀ i, i < m → 0 ≤ a (i + 1) - a i) :
    ∑ i ∈ Finset.range m, Real.arccos (Real.cos (a (i + 1) - a i))
      ≤ ∑ i ∈ Finset.range m, (a (i + 1) - a i) :=
  Finset.sum_le_sum (fun i hi =>
    arccos_cos_le_self _ (hnn i (Finset.mem_range.mp hi)))

/-- THE RESIDUE, CLOSED. `hcentral` FORCES the gap ceiling; it is not an extra assumption
that happens to be unavailable at `m <= 3`, it is equivalent to the conclusion there. -/
theorem gap_le_pi_of_central (m : ℕ) (a : ℕ → ℝ)
    (hnn : ∀ i, i < m → 0 ≤ a (i + 1) - a i)
    (hsum : ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi)
    (hcentral : ∑ i ∈ Finset.range m, Real.arccos (Real.cos (a (i + 1) - a i))
      = 2 * Real.pi) :
    ∀ i, i < m → a (i + 1) - a i ≤ Real.pi := by
  intro j hj
  by_contra hgt
  push_neg at hgt
  have hmem : j ∈ Finset.range m := Finset.mem_range.mpr hj
  have hlt : ∑ i ∈ Finset.range m, Real.arccos (Real.cos (a (i + 1) - a i))
      < ∑ i ∈ Finset.range m, (a (i + 1) - a i) := by
    refine Finset.sum_lt_sum (fun i hi =>
      arccos_cos_le_self _ (hnn i (Finset.mem_range.mp hi))) ⟨j, hmem, ?_⟩
    exact arccos_cos_lt_self _ hgt
  rw [hsum, hcentral] at hlt
  exact lt_irrefl _ hlt

/-- At ONE gap the central total is `arccos (cos 2π) = 0`, so `hcentral` is unsatisfiable. -/
theorem central_unsatisfiable_at_one (a : ℕ → ℝ)
    (hsum : ∑ i ∈ Finset.range 1, (a (i + 1) - a i) = 2 * Real.pi) :
    ∑ i ∈ Finset.range 1, Real.arccos (Real.cos (a (i + 1) - a i)) ≠ 2 * Real.pi := by
  have hpi := Real.pi_pos
  rw [Finset.sum_range_one] at hsum ⊢
  rw [hsum, show (2 * Real.pi) = 0 + 2 * Real.pi by ring, Real.cos_add_two_pi, Real.cos_zero,
      Real.arccos_one]
  intro hEq
  linarith

#print axioms arccos_cos_le_self
#print axioms gap_le_pi_of_central
#print axioms central_unsatisfiable_at_one
