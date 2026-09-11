import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry Finset

/-! # erdos:1084 upper -- O06 CORRECTED: the fan-triangulation interior-angle sum.

The frozen O06 is FALSE (O06_CollinearRefutation.lean): its `hcyclic` is a tautology and a
collinear re-ordering satisfies every hypothesis with angle sum `0`.  This file states the
theorem the scaffold's own header asked for and proves it.

The cyclic-order content is carried by an explicit interior point `v` and the ANGLE
ADDITION hypothesis `hadd`: the interior angle at each vertex splits at `v`.  That is the
honest form of "v sees the vertices in this cyclic order", and it is exactly what O02's
argument enumeration delivers for the hull vertices seen from an interior point.  OPEN OBLIGATION, DECLARED AND NOT CLAIMED: this file does NOT prove that `hadd` and
`hcentral` are non-vacuous, and does NOT prove that the collinear witness fails them.  Two
things are owed before this theorem may be read as the corrected O06 -- (i) a MODEL: a
genuine convex polygon with an interior point satisfying every hypothesis, and (ii) a
DERIVATION of `hcentral` and `hadd` from the repaired O02 for hull vertices seen from an
interior point.  Until both land this is a true theorem whose hypotheses are UNMEASURED.
-/

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

#print axioms o06_fan_angle_sum
