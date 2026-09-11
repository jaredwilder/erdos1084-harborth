import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset

/-! # erdos:1084 upper -- THE GAP CEILING.

O02 (repaired) delivers consecutive argument gaps that are each at least `π/3` and sum to
`2π`.  The fan form of O06 silently needs the OPPOSITE bound: every gap at most `π`, since
`arccos (cos t) = t` only on `[0, π]` (kernel receipts
`o02-gap-equals-central-angle-2026-09-05`, `o02-gap-above-pi-breaks-central-2026-09-05`).

This file DERIVES the ceiling from the floor.  With `m` gaps each at least `π/3` summing to
`2π`, every gap is at most `2π - (m-1)π/3`; for `m ≥ 4` that is at most `π`.  So the
ceiling is FREE whenever the centre has at least four neighbours, and `m ≤ 3` is the exact
residue.
-/

theorem gap_ceiling (m : ℕ) (a : ℕ → ℝ)
    (hfloor : ∀ i, i < m → Real.pi / 3 ≤ a (i + 1) - a i)
    (hsum : ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi)
    (i : ℕ) (hi : i < m) :
    a (i + 1) - a i ≤ 2 * Real.pi - ((m : ℝ) - 1) * (Real.pi / 3) := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have hsplit : (a (i + 1) - a i)
      + ∑ j ∈ (Finset.range m).erase i, (a (j + 1) - a j)
      = ∑ j ∈ Finset.range m, (a (j + 1) - a j) := Finset.add_sum_erase (Finset.range m) (fun j => a (j + 1) - a j) hmem
  have hcard : ((Finset.range m).erase i).card = m - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_range]
  have hlb : (((Finset.range m).erase i).card : ℝ) * (Real.pi / 3)
      ≤ ∑ j ∈ (Finset.range m).erase i, (a (j + 1) - a j) := by
    have := Finset.card_nsmul_le_sum ((Finset.range m).erase i)
      (fun j => a (j + 1) - a j) (Real.pi / 3)
      (fun j hj => hfloor j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj)))
    simpa [nsmul_eq_mul] using this
  rw [hcard] at hlb
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : 1 ≤ m := Nat.one_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
    push_cast [Nat.cast_sub this]
    ring
  rw [hm1] at hlb
  linarith [hsplit, hsum, hlb]

theorem gap_le_pi_of_four_le (m : ℕ) (hm : 4 ≤ m) (a : ℕ → ℝ)
    (hfloor : ∀ i, i < m → Real.pi / 3 ≤ a (i + 1) - a i)
    (hsum : ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi)
    (i : ℕ) (hi : i < m) :
    a (i + 1) - a i ≤ Real.pi := by
  have hc := gap_ceiling m a hfloor hsum i hi
  have hpi := Real.pi_pos
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- With every gap in `[0, π]` the central angles ARE the gaps, so they sum to `2π`:
this is exactly `hcentral` of the corrected O06. -/
theorem central_sum_of_gaps_le_pi (m : ℕ) (a : ℕ → ℝ)
    (hnn : ∀ i, i < m → 0 ≤ a (i + 1) - a i)
    (hle : ∀ i, i < m → a (i + 1) - a i ≤ Real.pi)
    (hsum : ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi) :
    ∑ i ∈ Finset.range m, Real.arccos (Real.cos (a (i + 1) - a i)) = 2 * Real.pi := by
  rw [← hsum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  exact Real.arccos_cos (hnn i hi') (hle i hi')

/-- The two halves joined: from the O02 floor alone, at four or more neighbours the central
angles sum to `2π`. -/
theorem central_sum_from_o02_floor (m : ℕ) (hm : 4 ≤ m) (a : ℕ → ℝ)
    (hfloor : ∀ i, i < m → Real.pi / 3 ≤ a (i + 1) - a i)
    (hsum : ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi) :
    ∑ i ∈ Finset.range m, Real.arccos (Real.cos (a (i + 1) - a i)) = 2 * Real.pi := by
  refine central_sum_of_gaps_le_pi m a (fun i hi => ?_)
    (gap_le_pi_of_four_le m hm a hfloor hsum) hsum
  have := hfloor i hi
  have := Real.pi_pos
  linarith

#print axioms gap_ceiling
#print axioms gap_le_pi_of_four_le
#print axioms central_sum_from_o02_floor
