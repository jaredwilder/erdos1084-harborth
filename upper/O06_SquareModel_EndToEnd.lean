import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry Finset

/-! # erdos:1084 upper -- THE MODEL that discharges the non-vacuity obligation on
`o06_fan_angle_sum` (O06_FanAngleSum_Corrected.lean).

The unit square with vertices at the four axis points and `v` the centre satisfies EVERY
hypothesis of the corrected O06: 4-periodicity, `v` distinct from each vertex, four right
central angles summing to `2π`, and each right interior angle splitting at `v` into two
angles of `π/4`.  So the corrected statement is NOT vacuous.
-/

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

noncomputable def S4 : ℕ → ℝ^ 2
  | 0 => pt2 1 0
  | 1 => pt2 0 1
  | 2 => pt2 (-1) 0
  | _ => pt2 0 (-1)

noncomputable def vtx (i : ℕ) : ℝ^ 2 := S4 (i % 4)

theorem arccos_inv_sqrt_two : Real.arccos (Real.sqrt 2)⁻¹ = Real.pi / 4 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 := by positivity
  have key : (Real.sqrt 2)⁻¹ = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]; field_simp; nlinarith
  rw [key, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- Every angle in this file reduces to `arccos` of an explicit rational. -/
macro "angle_calc" : tactic =>
  `(tactic| (rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
             norm_num [vtx, S4, pt2, EuclideanSpace.norm_eq, Fin.sum_univ_two, inner,
                       vsub_eq_sub, arccos_inv_sqrt_two]))

theorem sq_per (i : ℕ) : vtx (i + 4) = vtx i := by
  simp only [vtx]; congr 1; omega

theorem sq_ne (i : ℕ) : (pt2 0 0) ≠ vtx i := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  intro hEq
  rcases h with h | h | h | h <;>
    · simp only [vtx, h, S4, pt2] at hEq
      have hc := congrArg (fun z => (WithLp.ofLp z) 0) hEq
      have hd := congrArg (fun z => (WithLp.ofLp z) 1) hEq
      revert hc hd
      norm_num

theorem sq_central (i : ℕ) :
    EuclideanGeometry.angle (vtx i) (pt2 0 0) (vtx (i + 1)) = Real.pi / 2 := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  have h1 : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
  rcases h with h | h | h | h <;>
    · simp only [vtx, h, h1] <;> norm_num <;> angle_calc

theorem sq_interior (i : ℕ) :
    EuclideanGeometry.angle (vtx i) (vtx (i + 1)) (vtx (i + 2)) = Real.pi / 2 := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  have h1 : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
  have h2 : (i + 2) % 4 = (i % 4 + 2) % 4 := by omega
  rcases h with h | h | h | h <;>
    · simp only [vtx, h, h1, h2] <;> norm_num <;> angle_calc

theorem sq_half_left (i : ℕ) :
    EuclideanGeometry.angle (vtx i) (vtx (i + 1)) (pt2 0 0) = Real.pi / 4 := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  have h1 : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
  rcases h with h | h | h | h <;>
    · simp only [vtx, h, h1] <;> norm_num <;> angle_calc

theorem sq_half_right (i : ℕ) :
    EuclideanGeometry.angle (pt2 0 0) (vtx (i + 1)) (vtx (i + 2)) = Real.pi / 4 := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  have h1 : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
  have h2 : (i + 2) % 4 = (i % 4 + 2) % 4 := by omega
  rcases h with h | h | h | h <;>
    · simp only [vtx, h, h1, h2] <;> norm_num <;> angle_calc

/-- THE MODEL. Every hypothesis of `o06_fan_angle_sum` holds for the square and its centre. -/
theorem o06_fan_hypotheses_are_satisfiable :
    (∀ i, vtx (i + 4) = vtx i) ∧
    (∀ i, (pt2 0 0) ≠ vtx i) ∧
    (∑ i ∈ Finset.range 4, EuclideanGeometry.angle (vtx i) (pt2 0 0) (vtx (i + 1))
      = 2 * Real.pi) ∧
    (∀ i, EuclideanGeometry.angle (vtx i) (vtx (i + 1)) (vtx (i + 2))
      = EuclideanGeometry.angle (vtx i) (vtx (i + 1)) (pt2 0 0)
        + EuclideanGeometry.angle (pt2 0 0) (vtx (i + 1)) (vtx (i + 2))) := by
  refine ⟨sq_per, sq_ne, ?_, ?_⟩
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
    rw [sq_central 0, sq_central 1, sq_central 2, sq_central 3]
    ring
  · intro i
    rw [sq_interior i, sq_half_left i, sq_half_right i]
    ring

/-! ## END-TO-END: the corrected theorem applied to the model. -/

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

theorem o06_model_end_to_end :
    ∑ i ∈ Finset.range 4, EuclideanGeometry.angle (vtx i) (vtx (i + 1)) (vtx (i + 2))
      = ((4 : ℝ) - 2) * Real.pi := by
  obtain ⟨h1, h2, h3, h4⟩ := o06_fan_hypotheses_are_satisfiable
  simpa using o06_fan_angle_sum 4 (by norm_num) (pt2 0 0) vtx h1 h2 h3 h4

#print axioms o06_fan_hypotheses_are_satisfiable
#print axioms o06_model_end_to_end
