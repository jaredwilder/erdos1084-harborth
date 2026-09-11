import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O01, THE 60 DEGREE GAP

Two unit-distance edges at a common vertex of a 1-separated set subtend an angle of at
least `π / 3`.  This is the equilateral-triangle inequality, and it is the ONLY place the
1-separation hypothesis enters the angle argument.

STATUS: LADDER_ATTEMPT -- a complete proof is written; it has NOT been compiled (no Lean
on the authoring machine).  Route: `EuclideanGeometry.law_cos` (Mathlib) turns the chord
length into `2 - 2 cos θ`; `1 ≤ chord` gives `cos θ ≤ 1/2`; `Real.strictAntiOn_cos` on
`[0, π]` with `Real.cos_pi_div_three` turns that into `π / 3 ≤ θ`.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o01_sixty_degree_gap (x y z : ℝ^ 2)
    (hxy : dist x y = 1) (hxz : dist x z = 1) (hyz : 1 ≤ dist y z) :
    Real.pi / 3 ≤ EuclideanGeometry.angle y x z := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdyz : (0 : ℝ) ≤ dist y z := dist_nonneg
  have h0 : 0 ≤ EuclideanGeometry.angle y x z := EuclideanGeometry.angle_nonneg y x z
  have hle : EuclideanGeometry.angle y x z ≤ Real.pi := EuclideanGeometry.angle_le_pi y x z
  by_contra hcon
  push_neg at hcon
  have hmem1 : EuclideanGeometry.angle y x z ∈ Set.Icc 0 Real.pi := Set.mem_Icc.mpr ⟨h0, hle⟩
  have hmem2 : Real.pi / 3 ∈ Set.Icc 0 Real.pi := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hcos : Real.cos (Real.pi / 3) < Real.cos (EuclideanGeometry.angle y x z) :=
    Real.strictAntiOn_cos hmem1 hmem2 hcon
  rw [Real.cos_pi_div_three] at hcos
  have hlaw := EuclideanGeometry.law_cos y x z
  rw [dist_comm y x, dist_comm z x, hxy, hxz] at hlaw
  nlinarith [hlaw, hcos, hyz, hdyz]
