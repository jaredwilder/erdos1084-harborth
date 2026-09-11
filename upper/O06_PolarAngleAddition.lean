import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry

/-! # THE ANGLE-ADDITION LEMMA MATHLIB DOES NOT HAVE (plane, polar form).

A grep of `Mathlib/Geometry/Euclidean/Angle/` at rev `919544d4` finds only the
unconditional triangle INEQUALITY `EuclideanGeometry.angle_le_angle_add_angle`.  There is
no equality form for "the middle ray lies inside the angle".  This file supplies the plane
case in polar coordinates, which is the form the erdos:1084 fan argument needs.

STEP 1 is the sharpening of O02c: with both rays given by polar arguments about `v`, the
angle IS `arccos (cos (a - b))` -- an equality, where O02c gave only `≤ |a - b|`.
STEP 2 is then arithmetic, via `Real.arccos_cos` on `[0, π]`.
-/

theorem polar_angle_eq_arccos_cos (v u w : ℝ^ 2) (a b ru rw : ℝ)
    (hru : 0 < ru) (hrw : 0 < rw)
    (hu0 : u.ofLp 0 = v.ofLp 0 + ru * Real.cos a) (hu1 : u.ofLp 1 = v.ofLp 1 + ru * Real.sin a)
    (hw0 : w.ofLp 0 = v.ofLp 0 + rw * Real.cos b) (hw1 : w.ofLp 1 = v.ofLp 1 + rw * Real.sin b) :
    EuclideanGeometry.angle u v w = Real.arccos (Real.cos (a - b)) := by
  have hsa : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  have hsb : Real.sin b ^ 2 + Real.cos b ^ 2 = 1 := Real.sin_sq_add_cos_sq b
  rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
  congr 1
  have hinner : (inner ℝ (u -ᵥ v) (w -ᵥ v) : ℝ) = ru * rw * Real.cos (a - b) := by
    simp [inner, Fin.sum_univ_two, vsub_eq_sub, hu0, hu1, hw0, hw1, Real.cos_sub]
    ring
  have hnu : ‖u -ᵥ v‖ = ru := by
    rw [EuclideanSpace.norm_eq]
    simp only [vsub_eq_sub, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    rw [show (u - v).ofLp 0 ^ 2 + (u - v).ofLp 1 ^ 2 = ru ^ 2 by
      simp [hu0, hu1]; nlinarith [hsa]]
    exact Real.sqrt_sq hru.le
  have hnw : ‖w -ᵥ v‖ = rw := by
    rw [EuclideanSpace.norm_eq]
    simp only [vsub_eq_sub, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    rw [show (w - v).ofLp 0 ^ 2 + (w - v).ofLp 1 ^ 2 = rw ^ 2 by
      simp [hw0, hw1]; nlinarith [hsb]]
    exact Real.sqrt_sq hrw.le
  rw [hinner, hnu, hnw]
  field_simp



theorem arccos_cos_of_nonneg_le_pi (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ Real.pi) :
    Real.arccos (Real.cos t) = t := Real.arccos_cos h0 h1

/-- THE ANGLE-ADDITION EQUALITY. `y` lies inside the angle `∠ u v w` exactly when its polar
argument lies between the other two and no arc exceeds `π`; then the angle splits. -/
theorem polar_angle_add (v u y w : ℝ^ 2) (a b c ru ry rw : ℝ)
    (hru : 0 < ru) (hry : 0 < ry) (hrw : 0 < rw)
    (hu0 : u.ofLp 0 = v.ofLp 0 + ru * Real.cos a) (hu1 : u.ofLp 1 = v.ofLp 1 + ru * Real.sin a)
    (hy0 : y.ofLp 0 = v.ofLp 0 + ry * Real.cos b) (hy1 : y.ofLp 1 = v.ofLp 1 + ry * Real.sin b)
    (hw0 : w.ofLp 0 = v.ofLp 0 + rw * Real.cos c) (hw1 : w.ofLp 1 = v.ofLp 1 + rw * Real.sin c)
    (hab : 0 ≤ b - a) (hab' : b - a ≤ Real.pi)
    (hbc : 0 ≤ c - b) (hbc' : c - b ≤ Real.pi)
    (hac' : c - a ≤ Real.pi) :
    EuclideanGeometry.angle u v y + EuclideanGeometry.angle y v w
      = EuclideanGeometry.angle u v w := by
  have e1 := polar_angle_eq_arccos_cos v u y a b ru ry hru hry hu0 hu1 hy0 hy1
  have e2 := polar_angle_eq_arccos_cos v y w b c ry rw hry hrw hy0 hy1 hw0 hw1
  have e3 := polar_angle_eq_arccos_cos v u w a c ru rw hru hrw hu0 hu1 hw0 hw1
  have c1 : Real.cos (a - b) = Real.cos (b - a) := by
    rw [show a - b = -(b - a) by ring, Real.cos_neg]
  have c2 : Real.cos (b - c) = Real.cos (c - b) := by
    rw [show b - c = -(c - b) by ring, Real.cos_neg]
  have c3 : Real.cos (a - c) = Real.cos (c - a) := by
    rw [show a - c = -(c - a) by ring, Real.cos_neg]
  rw [e1, e2, e3, c1, c2, c3,
      arccos_cos_of_nonneg_le_pi _ hab hab',
      arccos_cos_of_nonneg_le_pi _ hbc hbc',
      arccos_cos_of_nonneg_le_pi _ (by linarith) hac']
  ring

#print axioms polar_angle_eq_arccos_cos
#print axioms polar_angle_add
