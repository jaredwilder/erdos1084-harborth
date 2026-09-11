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

/-! ## THE CONSUMER END, ready for the H-rungs.

`o06_angle_sum_of_interior_point` still takes `hcentral` and `hvne` as INPUTS.  H2 will
produce polar data about the interior point, not an angle sum, so this file converts once
and for all: from a polar description of the listing about `v` with the gap bounds and the
`2π` gap total, BOTH `hcentral` and `hvne` are derived, and only `InsideAngleAt` remains as
an input for H3 to supply.

`O02_CentralForcesCeiling.lean` shows the gap ceiling here is not an extra ask: it is
EQUIVALENT to the `hcentral` this theorem produces.
-/

/-- `v` is not one of the listed points, because every radius is positive. -/
theorem ne_of_pos_radius (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v.ofLp 1 + r i * Real.sin (a i)) :
    ∀ i, v ≠ p i := by
  intro i hEq
  have e0 : r i * Real.cos (a i) = 0 := by have := hp0 i; rw [← hEq] at this; linarith
  have e1 : r i * Real.sin (a i) = 0 := by have := hp1 i; rw [← hEq] at this; linarith
  have hri := (hr i).ne'
  have hc : Real.cos (a i) = 0 := by
    rcases mul_eq_zero.mp e0 with h | h
    · exact absurd h hri
    · exact h
  have hs : Real.sin (a i) = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h hri
    · exact h
  have := Real.sin_sq_add_cos_sq (a i)
  rw [hc, hs] at this
  norm_num at this

/-- `hcentral` from the polar data. -/
theorem hcentral_of_polar (m : ℕ) (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v.ofLp 1 + r i * Real.sin (a i))
    (hnn : ∀ i, i < m → 0 ≤ a (i + 1) - a i)
    (hle : ∀ i, i < m → a (i + 1) - a i ≤ Real.pi)
    (hsum : ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi) :
    ∑ i ∈ Finset.range m, EuclideanGeometry.angle (p i) v (p (i + 1)) = 2 * Real.pi := by
  rw [← hsum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  have hpol := polar_angle_eq_arccos_cos v (p i) (p (i + 1)) (a i) (a (i + 1))
    (r i) (r (i + 1)) (hr i) (hr (i + 1)) (hp0 i) (hp1 i) (hp0 (i + 1)) (hp1 (i + 1))
  rw [hpol, show Real.cos (a i - a (i + 1)) = Real.cos (a (i + 1) - a i) by
    rw [show a i - a (i + 1) = -(a (i + 1) - a i) by ring, Real.cos_neg]]
  exact Real.arccos_cos (hnn i hi') (hle i hi')

/-- THE HANDOFF OBJECT. Everything but `InsideAngleAt` is now derived from polar data. -/
theorem o06_angle_sum_of_polar_fan (h : ℕ) (hh : 3 ≤ h) (v : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (a r : ℕ → ℝ)
    (hper : ∀ i, p (i + h) = p i)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v.ofLp 1 + r i * Real.sin (a i))
    (hnn : ∀ i, i < h → 0 ≤ a (i + 1) - a i)
    (hle : ∀ i, i < h → a (i + 1) - a i ≤ Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a (i + 1) - a i) = 2 * Real.pi)
    (hinside : ∀ i, InsideAngleAt v p i) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi :=
  o06_angle_sum_of_interior_point h hh v p hper
    (ne_of_pos_radius v p a r hr hp0 hp1)
    (hcentral_of_polar h v p a r hr hp0 hp1 hnn hle hgap)
    hinside

#print axioms ne_of_pos_radius
#print axioms hcentral_of_polar
#print axioms o06_angle_sum_of_polar_fan
