import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O02c, ANGLE ≤ ARGUMENT GAP

If `u` and `w` are at distance `1` from `v` and their chord satisfies the unit-circle
chord identity `dist u w ^ 2 = 2 - 2 cos (a - b)`, then the geometric angle at `v` is at
most `|a - b|`.

This is what makes a pigeonhole on ARGUMENTS a statement about ANGLES.  The `harccos`
binder is exactly the conclusion of O02b: it is carried as a hypothesis rather than
re-proved so that this file assumes nothing it does not name.

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o02c_angle_le_arg_gap (v u w : ℝ^ 2) (a b : ℝ)
    (hu : dist v u = 1) (hw : dist v w = 1)
    (hd : dist u w ^ 2 = 2 - 2 * Real.cos (a - b))
    (harccos : ∀ t : ℝ, Real.arccos (Real.cos t) ≤ |t|) :
    EuclideanGeometry.angle u v w ≤ |a - b| := by
  have h0 : 0 ≤ EuclideanGeometry.angle u v w := EuclideanGeometry.angle_nonneg u v w
  have hle : EuclideanGeometry.angle u v w ≤ Real.pi := EuclideanGeometry.angle_le_pi u v w
  have hlaw := EuclideanGeometry.law_cos u v w
  rw [dist_comm u v, dist_comm w v, hu, hw] at hlaw
  have hsq : dist u w ^ 2 = dist u w * dist u w := by ring
  rw [hsq] at hd
  have hcosang : Real.cos (EuclideanGeometry.angle u v w) = Real.cos (a - b) := by
    linarith [hlaw, hd]
  have hid : EuclideanGeometry.angle u v w
      = Real.arccos (Real.cos (EuclideanGeometry.angle u v w)) :=
    (Real.arccos_cos h0 hle).symm
  rw [hid, hcosang]
  exact harccos (a - b)
