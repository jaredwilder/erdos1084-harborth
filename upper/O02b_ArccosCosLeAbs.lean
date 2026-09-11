import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O02b, THE ARITHMETIC CORE OF THE GAP BOUND

`arccos (cos t) ≤ |t|` for every real `t`.

THIS FOUR-LINE LEMMA IS THE PRIMITIVE THE CAMPAIGN REPORT CALLED "NOT IN MATHLIB, THE
BLOCKER".  It is not a cyclic-order theory: it is `Real.arccos_cos` on `[0, π]` and
`Real.arccos_le_pi` outside it.  It says exactly what the ladder needs -- the geometric
angle between two unit vectors never EXCEEDS their argument gap -- and the ladder needs
only that inequality, never the equality.

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

theorem o02b_arccos_cos_le_abs (t : ℝ) : Real.arccos (Real.cos t) ≤ |t| := by
  have hcos : Real.cos t = Real.cos |t| := by
    rcases abs_cases t with ⟨hb, _⟩ | ⟨hb, _⟩
    · rw [hb]
    · rw [hb, Real.cos_neg]
  rcases le_or_gt |t| Real.pi with h | h
  · rw [hcos, Real.arccos_cos (abs_nonneg t) h]
  · exact le_trans (Real.arccos_le_pi (Real.cos t)) h.le
