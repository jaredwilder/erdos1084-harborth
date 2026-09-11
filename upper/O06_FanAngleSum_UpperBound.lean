import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry Finset

/-! # erdos:1084 upper -- O06, THE HYPOTHESIS-FREE HALF.

`o06_fan_angle_sum` (O06_FanAngleSum_Corrected.lean) needs `hadd`: the interior angle at
each vertex SPLITS at `v`.  Mathlib has no angle-addition-under-betweenness lemma -- a
search of `Mathlib/Geometry/Euclidean/Angle/` finds only the triangle INEQUALITY
`EuclideanGeometry.angle_le_angle_add_angle`, which is unconditional.

That inequality is enough for one direction, and it costs NO hypothesis at all: the
interior-angle sum of ANY listing with a `2π` central-angle total is AT MOST `(h-2)π`.
`hadd` is exactly what upgrades this to equality, and it remains the open obligation.
-/

theorem o06_fan_angle_sum_le (h : ℕ) (v : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (hper : ∀ i, p (i + h) = p i)
    (hvne : ∀ i, v ≠ p i)
    (hcentral : ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1))
        = 2 * Real.pi) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      ≤ ((h : ℝ) - 2) * Real.pi := by
  set b : ℕ → ℝ := fun i => EuclideanGeometry.angle v (p (i + 1)) (p i) with hb
  set g : ℕ → ℝ := fun i => EuclideanGeometry.angle (p (i + 1)) (p i) v with hg
  have tri : ∀ i, EuclideanGeometry.angle (p i) v (p (i + 1)) + b i + g i = Real.pi := by
    intro i
    simpa [hb, hg] using
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := p i) (p₂ := v)
        (p (i + 1)) (hvne i)
  have hsum : (∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1)))
      + (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g i) = (h : ℝ) * Real.pi := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp [tri, Finset.sum_const, Finset.card_range, mul_comm]
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
  -- the ONLY geometric input, and it is unconditional
  have hle : ∀ i, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      ≤ b i + g (i + 1) := by
    intro i
    have key := EuclideanGeometry.angle_le_angle_add_angle (p (i + 1)) (p i) v (p (i + 2))
    have e1 : EuclideanGeometry.angle (p i) (p (i + 1)) v = b i := by
      simpa [hb] using EuclideanGeometry.angle_comm (p i) (p (i + 1)) v
    have e2 : EuclideanGeometry.angle v (p (i + 1)) (p (i + 2)) = g (i + 1) := by
      simpa [hg, add_assoc] using EuclideanGeometry.angle_comm v (p (i + 1)) (p (i + 2))
    rw [e1, e2] at key
    exact key
  calc ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      ≤ ∑ i ∈ Finset.range h, (b i + g (i + 1)) :=
        Finset.sum_le_sum (fun i _ => hle i)
    _ = (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g (i + 1)) :=
        Finset.sum_add_distrib
    _ = (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g i) := by rw [hshift]
    _ = ((h : ℝ) - 2) * Real.pi := by rw [hcentral] at hsum; linarith

#print axioms o06_fan_angle_sum_le
