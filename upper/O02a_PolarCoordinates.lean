import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O02a, POLAR COORDINATES FOR A UNIT VECTOR IN THE PLANE

Every point of the unit circle is `(cos t, sin t)` for a unique `t ∈ (-π, π]`.  This is
the first half of O2: it is what gives each unit-distance neighbour of a vertex an
ANGLE, which is the object the cyclic order is an order on.

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.  Route:
`t := arccos x` when `y ≥ 0` and `t := -arccos x` when `y < 0`; `Real.cos_arccos` and
`Real.sin_arccos` supply the two coordinates, and `arccos x = π` is excluded in the
second branch because it would force `y = 0`.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

theorem o02a_polar_coordinates (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    ∃ t : ℝ, -Real.pi < t ∧ t ≤ Real.pi ∧ Real.cos t = x ∧ Real.sin t = y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx1 hx2
  have hsin : Real.sin (Real.arccos x) = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  have habs : Real.sqrt (1 - x ^ 2) = |y| := by
    rw [show (1 : ℝ) - x ^ 2 = y ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  have h0 : 0 ≤ Real.arccos x := Real.arccos_nonneg x
  have hup : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
  rcases le_or_gt 0 y with hy | hy
  · refine ⟨Real.arccos x, by linarith, hup, hcos, ?_⟩
    rw [hsin, habs, abs_of_nonneg hy]
  · have hne : Real.arccos x ≠ Real.pi := by
      intro hEq
      have hz : Real.sin (Real.arccos x) = 0 := by rw [hEq, Real.sin_pi]
      rw [hsin, habs] at hz
      have hy0 : y = 0 := abs_eq_zero.mp hz
      linarith
    have hlt : Real.arccos x < Real.pi := lt_of_le_of_ne hup hne
    refine ⟨-Real.arccos x, by linarith, by linarith, ?_, ?_⟩
    · rw [Real.cos_neg]
      exact hcos
    · rw [Real.sin_neg, hsin, habs, abs_of_neg hy]
      ring
