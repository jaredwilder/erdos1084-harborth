/-
H01_Degenerate -- rung H1 of the hull-angle development (coordinator, 2026-09-05, v3)

Statement FROZEN from H00_HullAngle_SCAFFOLD.lean: a 1-separated set whose convex hull
has EMPTY interior gives every point at most two unit-distance neighbours.

Route: the sealed O04 chain verbatim (empty interior ⟹ affineSpan ≠ ⊤ ⟹ vectorSpan ≠ ⊤
⟹ nonzero normal w), then plane algebra: each neighbour offset x is orthogonal to w and
unit; with t := (−b·x₀ + a·x₁)/n the three linear_combination certificates
  a·hinner, b·hinner, (a²+b²)·hnorm − (a·x₀+b·x₁)·hinner
pin x = t·(−b,a)/n and t² = 1 — two candidate points, card ≤ 2.  Separation unused.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)
end Metric

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Erdos1084Upper

noncomputable def nbrs (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : Finset (ℝ^ 2) :=
  {u ∈ S | dist v u = 1}

noncomputable def udeg (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : ℕ := (nbrs S v).card

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

@[simp] lemma pt2_zero (x y : ℝ) : (pt2 x y).ofLp 0 = x := rfl
@[simp] lemma pt2_one (x y : ℝ) : (pt2 x y).ofLp 1 = y := rfl

theorem h1_degenerate_udeg_le_two (S : Finset (ℝ^ 2))
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hdeg : interior (convexHull ℝ (S : Set (ℝ^ 2))) = ∅)
    (v : ℝ^ 2) (hv : v ∈ S) :
    udeg S v ≤ 2 := by
  classical
  have hv' : v ∈ (S : Set (ℝ^ 2)) := Finset.mem_coe.mpr hv
  -- === the sealed O04 chain, verbatim names ===
  have hint : ¬ (interior (convexHull ℝ (S : Set (ℝ^ 2)))).Nonempty := by
    rw [hdeg]
    exact Set.not_nonempty_empty
  have hspanS : affineSpan ℝ (S : Set (ℝ^ 2)) ≠ ⊤ := fun h =>
    hint (interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr h)
  have hSne : (S : Set (ℝ^ 2)).Nonempty := ⟨v, hv'⟩
  have hWne : vectorSpan ℝ (S : Set (ℝ^ 2)) ≠ ⊤ := by
    intro h
    refine hspanS ?_
    first
      | exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
          (k := ℝ) (hs := hSne)).mpr h
      | exact (affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
          (k := ℝ) (hs := hSne)).mpr h
      | exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
          ℝ (ℝ^ 2) (ℝ^ 2) hSne).mpr h
  have horth : (vectorSpan ℝ (S : Set (ℝ^ 2)))ᗮ ≠ ⊥ := fun h =>
    hWne (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff _).mp horth
  -- === coordinates of the normal ===
  set a : ℝ := w.ofLp 0 with ha
  set b : ℝ := w.ofLp 1 with hb
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h
    apply hw0
    have h0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have h1 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    ext i
    fin_cases i
    · simpa [ha] using h0
    · simpa [hb] using h1
  have habpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hab)
  set n : ℝ := Real.sqrt (a ^ 2 + b ^ 2) with hn
  have hnpos : 0 < n := Real.sqrt_pos.mpr habpos
  have hnne : n ≠ 0 := ne_of_gt hnpos
  have hnsq : n ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt habpos.le
  set cpos : ℝ^ 2 := pt2 (v.ofLp 0 + (-b) / n) (v.ofLp 1 + a / n) with hcposdef
  set cneg : ℝ^ 2 := pt2 (v.ofLp 0 + b / n) (v.ofLp 1 + (-a) / n) with hcnegdef
  -- === every unit neighbour is one of the two candidates ===
  have hkey : ∀ u ∈ nbrs S v, u = cpos ∨ u = cneg := by
    intro u hu
    obtain ⟨huS, hdist⟩ := Finset.mem_filter.mp hu
    have hu' : u ∈ (S : Set (ℝ^ 2)) := Finset.mem_coe.mpr huS
    have hdiff : u - v ∈ vectorSpan ℝ (S : Set (ℝ^ 2)) := by
      have h1 := vsub_mem_vectorSpan (k := ℝ) (hp₁ := hu') (hp₂ := hv')
      simpa [vsub_eq_sub] using h1
    have hzero : (inner ℝ w (u - v) : ℝ) = 0 :=
      (Submodule.mem_orthogonal' _ w).mp hwmem _ hdiff
    set x0 : ℝ := u.ofLp 0 - v.ofLp 0 with hx0
    set x1 : ℝ := u.ofLp 1 - v.ofLp 1 with hx1
    have hip : (inner ℝ w (u - v) : ℝ) = a * x0 + b * x1 := by
      simp only [inner, Fin.sum_univ_two]
      simp [ha, hb, hx0, hx1]
      ring
    have hinner : a * x0 + b * x1 = 0 := by
      rw [← hip]
      exact hzero
    have hnorm : x0 ^ 2 + x1 ^ 2 = 1 := by
      have h1 : dist u v = 1 := by
        rw [dist_comm]
        exact hdist
      have h2 : dist u v ^ 2 = x0 ^ 2 + x1 ^ 2 := by
        rw [EuclideanSpace.dist_eq,
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
        simp [Fin.sum_univ_two, hx0, hx1, sq_abs, Real.dist_eq]
      rw [h1] at h2
      nlinarith [h2]
    set t : ℝ := (-b * x0 + a * x1) / n with ht
    have e0 : x0 * n ^ 2 = (-b * x0 + a * x1) * (-b) := by
      rw [hnsq]
      linear_combination a * hinner
    have e1 : x1 * n ^ 2 = (-b * x0 + a * x1) * a := by
      rw [hnsq]
      linear_combination b * hinner
    have e2 : (-b * x0 + a * x1) ^ 2 = n ^ 2 := by
      rw [hnsq]
      linear_combination (a ^ 2 + b ^ 2) * hnorm - (a * x0 + b * x1) * hinner
    have ht2 : t ^ 2 = 1 := by
      rw [ht]
      field_simp
      linear_combination e2
    have hx0t : x0 = t * (-b / n) := by
      rw [ht]
      field_simp
      linear_combination e0
    have hx1t : x1 = t * (a / n) := by
      rw [ht]
      field_simp
      linear_combination e1
    have hcase : t = 1 ∨ t = -1 := by
      have hfac : (t - 1) * (t + 1) = 0 := by linear_combination ht2
      rcases mul_eq_zero.mp hfac with h | h
      · left; linarith
      · right; linarith
    rcases hcase with h1 | h1
    · left
      ext i
      fin_cases i
      · show u.ofLp 0 = cpos.ofLp 0
        rw [hcposdef, pt2_zero]
        have := hx0t
        rw [h1] at this
        rw [hx0] at this
        linarith
      · show u.ofLp 1 = cpos.ofLp 1
        rw [hcposdef, pt2_one]
        have := hx1t
        rw [h1] at this
        rw [hx1] at this
        linarith
    · right
      ext i
      fin_cases i
      · show u.ofLp 0 = cneg.ofLp 0
        rw [hcnegdef, pt2_zero]
        have := hx0t
        rw [h1] at this
        rw [hx0] at this
        have hbn : -1 * (-b / n) = b / n := by ring
        linarith [this, hbn]
      · show u.ofLp 1 = cneg.ofLp 1
        rw [hcnegdef, pt2_one]
        have := hx1t
        rw [h1] at this
        rw [hx1] at this
        have han : -1 * (a / n) = -a / n := by ring
        linarith [this, han]
  -- === card bound from the two-element cover ===
  have hsubset : nbrs S v ⊆ ({cpos, cneg} : Finset (ℝ^ 2)) := by
    intro u hu
    rcases hkey u hu with h | h <;> simp [h]
  calc udeg S v = (nbrs S v).card := rfl
    _ ≤ ({cpos, cneg} : Finset (ℝ^ 2)).card := Finset.card_le_card hsubset
    _ ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp

end Erdos1084Upper

#print axioms Erdos1084Upper.h1_degenerate_udeg_le_two
