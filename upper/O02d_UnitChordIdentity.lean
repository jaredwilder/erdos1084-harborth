import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O02d, THE UNIT-CIRCLE CHORD IDENTITY

Two points at polar angles `a` and `b` on the unit circle centred at `v` are at squared
distance `2 - 2 cos (a - b)`.  This is the hypothesis `hd` that O02c consumes; together
O02a + O02d + O02c say "angle ≤ argument gap" with no hypothesis left over.

The coordinate access is `.ofLp`, matching the kernel-sealed lower-bound file's
`dist_P_sq` (the same `EuclideanSpace.dist_eq` / `Real.sq_sqrt` / `Fin.sum_univ_two`
pattern that already compiled on the box for this campaign).

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o02d_unit_chord_identity (v u w : ℝ^ 2) (a b : ℝ)
    (hu0 : u.ofLp 0 = v.ofLp 0 + Real.cos a) (hu1 : u.ofLp 1 = v.ofLp 1 + Real.sin a)
    (hw0 : w.ofLp 0 = v.ofLp 0 + Real.cos b) (hw1 : w.ofLp 1 = v.ofLp 1 + Real.sin b) :
    dist u w ^ 2 = 2 - 2 * Real.cos (a - b) := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, hu0, hu1, hw0, hw1, Real.cos_sub]
  linear_combination Real.sin_sq_add_cos_sq a + Real.sin_sq_add_cos_sq b
