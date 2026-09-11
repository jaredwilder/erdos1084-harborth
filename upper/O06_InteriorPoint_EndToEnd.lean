import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry Finset

/-! # erdos:1084 upper -- O06 WITH `hadd` DERIVED, not assumed.

`o06_fan_angle_sum` ASSUMES the interior angle at each vertex splits at `v`.  That is an
angle identity, and assuming an identity is weak.  This file replaces it by the ordinary
GEOMETRIC condition "v lies inside the angle at that vertex", written in the standard polar
form about the vertex, and DERIVES the split from `polar_angle_add`.

The remaining hypotheses are unchanged: h-periodicity, `v` distinct from every vertex, and
the central angles summing to `2π` (which `O02_GapCeiling.lean` derives from the O02 gap
floor whenever the centre has at least four neighbours).
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

theorem o06_fan_angle_sum (h : ℕ) (hh : 3 ≤ h) (v : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (hper : ∀ i, p (i + h) = p i)
    (hvne : ∀ i, v ≠ p i)
    (hcentral : ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1))
        = 2 * Real.pi)
    (hadd : ∀ i, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
        = EuclideanGeometry.angle (p i) (p (i + 1)) v
          + EuclideanGeometry.angle v (p (i + 1)) (p (i + 2))) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi := by
  set b : ℕ → ℝ := fun i => EuclideanGeometry.angle v (p (i + 1)) (p i) with hb
  set g : ℕ → ℝ := fun i => EuclideanGeometry.angle (p (i + 1)) (p i) v with hg
  -- the triangle v, p i, p (i+1)
  have tri : ∀ i, EuclideanGeometry.angle (p i) v (p (i + 1)) + b i + g i = Real.pi := by
    intro i
    simpa [hb, hg] using
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := p i) (p₂ := v)
        (p (i + 1)) (hvne i)
  have hsum : (∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1)))
      + (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g i) = (h : ℝ) * Real.pi := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp [tri, Finset.sum_const, Finset.card_range, mul_comm]
  -- g is h-periodic, so shifting the index does not move its sum
  have hgper : g h = g 0 := by
    have h1 : p (0 + h) = p 0 := hper 0
    have h2 : p (1 + h) = p 1 := hper 1
    simp only [hg]
    rw [show h + 1 = 1 + h by ring, h2, show h = 0 + h by ring, h1]
  have hshift : ∑ i ∈ Finset.range h, g (i + 1) = ∑ i ∈ Finset.range h, g i := by
    have e1 : ∑ i ∈ Finset.range (h + 1), g i
        = (∑ i ∈ Finset.range h, g (i + 1)) + g 0 := Finset.sum_range_succ' g h
    have e2 : ∑ i ∈ Finset.range (h + 1), g i
        = (∑ i ∈ Finset.range h, g i) + g h := Finset.sum_range_succ g h
    rw [hgper] at e2
    linarith [e1, e2]
  -- the interior angle at p (i+1) splits at v into b i and g (i+1)
  have hsplit : ∀ i, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = b i + g (i + 1) := by
    intro i
    rw [hadd i]
    congr 1
    · simpa [hb] using EuclideanGeometry.angle_comm (p i) (p (i + 1)) v
    · simpa [hg, add_assoc] using EuclideanGeometry.angle_comm v (p (i + 1)) (p (i + 2))
  calc ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ∑ i ∈ Finset.range h, (b i + g (i + 1)) := by
        exact Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g (i + 1)) :=
        Finset.sum_add_distrib
    _ = (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g i) := by rw [hshift]
    _ = ((h : ℝ) - 2) * Real.pi := by rw [hcentral] at hsum; linarith

/-- `v` lies inside the angle at `p (i+1)`, stated in polar coordinates ABOUT that vertex. -/
def InsideAngleAt (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (i : ℕ) : Prop :=
  ∃ α β γ r₁ r₂ r₃ : ℝ,
    0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
    (p i).ofLp 0 = (p (i + 1)).ofLp 0 + r₁ * Real.cos α ∧
    (p i).ofLp 1 = (p (i + 1)).ofLp 1 + r₁ * Real.sin α ∧
    v.ofLp 0 = (p (i + 1)).ofLp 0 + r₂ * Real.cos β ∧
    v.ofLp 1 = (p (i + 1)).ofLp 1 + r₂ * Real.sin β ∧
    (p (i + 2)).ofLp 0 = (p (i + 1)).ofLp 0 + r₃ * Real.cos γ ∧
    (p (i + 2)).ofLp 1 = (p (i + 1)).ofLp 1 + r₃ * Real.sin γ ∧
    0 ≤ β - α ∧ β - α ≤ Real.pi ∧ 0 ≤ γ - β ∧ γ - β ≤ Real.pi ∧ γ - α ≤ Real.pi

/-- `hadd` is a CONSEQUENCE of `v` lying inside the angle. -/
theorem hadd_of_inside (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (i : ℕ) (h : InsideAngleAt v p i) :
    EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = EuclideanGeometry.angle (p i) (p (i + 1)) v
        + EuclideanGeometry.angle v (p (i + 1)) (p (i + 2)) := by
  obtain ⟨α, β, γ, r₁, r₂, r₃, h₁, h₂, h₃, e1, e2, e3, e4, e5, e6, b1, b2, b3, b4, b5⟩ := h
  exact (polar_angle_add (p (i + 1)) (p i) v (p (i + 2)) α β γ r₁ r₂ r₃
    h₁ h₂ h₃ e1 e2 e3 e4 e5 e6 b1 b2 b3 b4 b5).symm

/-- THE CORRECTED O06, with the angle split DERIVED from an ordinary geometric hypothesis. -/
theorem o06_angle_sum_of_interior_point (h : ℕ) (hh : 3 ≤ h) (v : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (hper : ∀ i, p (i + h) = p i)
    (hvne : ∀ i, v ≠ p i)
    (hcentral : ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1))
        = 2 * Real.pi)
    (hinside : ∀ i, InsideAngleAt v p i) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi :=
  o06_fan_angle_sum h hh v p hper hvne hcentral (fun i => hadd_of_inside v p i (hinside i))

/-! ## THE MODEL for `InsideAngleAt`: the CLOCKWISE square about its centre. -/

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

/-- Clockwise, so that the polar arguments about each vertex INCREASE along the listing. -/
noncomputable def W4 : ℕ → ℝ^ 2
  | 0 => pt2 1 0
  | 1 => pt2 0 (-1)
  | 2 => pt2 (-1) 0
  | _ => pt2 0 1

noncomputable def ww (i : ℕ) : ℝ^ 2 := W4 (i % 4)

theorem sq2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith

theorem c34 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show (3 * Real.pi / 4) = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_four]
theorem s34 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [show (3 * Real.pi / 4) = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_four]
theorem c54 : Real.cos (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show (5 * Real.pi / 4) = Real.pi / 4 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_four]
theorem s54 : Real.sin (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show (5 * Real.pi / 4) = Real.pi / 4 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_four]
theorem cm14 : Real.cos (-(Real.pi / 4)) = Real.sqrt 2 / 2 := by
  rw [Real.cos_neg, Real.cos_pi_div_four]
theorem sm14 : Real.sin (-(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  rw [Real.sin_neg, Real.sin_pi_div_four]
theorem cm34 : Real.cos (-(3 * Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  rw [Real.cos_neg, c34]
theorem sm34 : Real.sin (-(3 * Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  rw [Real.sin_neg, s34]
theorem cm12 : Real.cos (-(Real.pi / 2)) = 0 := by rw [Real.cos_neg, Real.cos_pi_div_two]
theorem sm12 : Real.sin (-(Real.pi / 2)) = -1 := by rw [Real.sin_neg, Real.sin_pi_div_two]

theorem ww_inside (i : ℕ) : InsideAngleAt (pt2 0 0) ww i := by
  have hpi := Real.pi_pos
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  have h1 : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
  have h2 : (i + 2) % 4 = (i % 4 + 2) % 4 := by omega
  rcases h with h | h | h | h
  · exact ⟨Real.pi / 4, Real.pi / 2, 3 * Real.pi / 4, Real.sqrt 2, 1, Real.sqrt 2,
      by positivity, by norm_num, by positivity, by
        simp [ww, h, h1, h2, W4, pt2, Real.cos_pi_div_four]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, Real.sin_pi_div_four]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, Real.cos_pi_div_two], by
        simp [ww, h, h1, h2, W4, pt2, Real.sin_pi_div_two], by
        simp [ww, h, h1, h2, W4, pt2, c34]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, s34]; nlinarith [sq2],
      by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · exact ⟨-(Real.pi / 4), 0, Real.pi / 4, Real.sqrt 2, 1, Real.sqrt 2,
      by positivity, by norm_num, by positivity, by
        simp [ww, h, h1, h2, W4, pt2, cm14]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, sm14]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2], by
        simp [ww, h, h1, h2, W4, pt2], by
        simp [ww, h, h1, h2, W4, pt2, Real.cos_pi_div_four]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, Real.sin_pi_div_four]; nlinarith [sq2],
      by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · exact ⟨-(3 * Real.pi / 4), -(Real.pi / 2), -(Real.pi / 4), Real.sqrt 2, 1, Real.sqrt 2,
      by positivity, by norm_num, by positivity, by
        simp [ww, h, h1, h2, W4, pt2, cm34, c34]; nlinarith [sq2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)], by
        simp [ww, h, h1, h2, W4, pt2, sm34, s34]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, cm12], by
        simp [ww, h, h1, h2, W4, pt2, sm12], by
        simp [ww, h, h1, h2, W4, pt2, cm14]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, sm14]; nlinarith [sq2],
      by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · exact ⟨3 * Real.pi / 4, Real.pi, 5 * Real.pi / 4, Real.sqrt 2, 1, Real.sqrt 2,
      by positivity, by norm_num, by positivity, by
        simp [ww, h, h1, h2, W4, pt2, c34]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, s34]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2], by
        simp [ww, h, h1, h2, W4, pt2], by
        simp [ww, h, h1, h2, W4, pt2, c54]; nlinarith [sq2], by
        simp [ww, h, h1, h2, W4, pt2, s54]; nlinarith [sq2],
      by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem arccos_inv_sqrt_two : Real.arccos (Real.sqrt 2)⁻¹ = Real.pi / 4 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 := by positivity
  have key : (Real.sqrt 2)⁻¹ = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]; field_simp; nlinarith
  rw [key, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

macro "angle_calc" : tactic =>
  `(tactic| (rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
             norm_num [ww, W4, pt2, EuclideanSpace.norm_eq, Fin.sum_univ_two, inner,
                       vsub_eq_sub, arccos_inv_sqrt_two]))

theorem ww_per (i : ℕ) : ww (i + 4) = ww i := by
  simp only [ww]; congr 1; omega

theorem ww_ne (i : ℕ) : (pt2 0 0) ≠ ww i := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  intro hEq
  rcases h with h | h | h | h <;>
    · simp only [ww, h, W4, pt2] at hEq
      have hc := congrArg (fun z => (WithLp.ofLp z) 0) hEq
      have hd := congrArg (fun z => (WithLp.ofLp z) 1) hEq
      revert hc hd
      norm_num

theorem ww_central (i : ℕ) :
    EuclideanGeometry.angle (ww i) (pt2 0 0) (ww (i + 1)) = Real.pi / 2 := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  have h1 : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
  rcases h with h | h | h | h <;>
    · simp only [ww, h, h1] <;> norm_num <;> angle_calc

/-- THE FULL CORRECTED O06, END TO END, WITH NO ASSUMED ANGLE IDENTITY. -/
theorem o06_square_end_to_end :
    ∑ i ∈ Finset.range 4,
        EuclideanGeometry.angle (ww i) (ww (i + 1)) (ww (i + 2)) = ((4 : ℝ) - 2) * Real.pi := by
  have hcentral : ∑ i ∈ Finset.range 4,
      EuclideanGeometry.angle (ww i) (pt2 0 0) (ww (i + 1)) = 2 * Real.pi := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
    rw [ww_central 0, ww_central 1, ww_central 2, ww_central 3]
    ring
  simpa using
    o06_angle_sum_of_interior_point 4 (by norm_num) (pt2 0 0) ww ww_per ww_ne hcentral ww_inside

#print axioms ww_inside
#print axioms o06_square_end_to_end
