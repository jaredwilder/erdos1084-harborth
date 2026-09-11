import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry

/-! # erdos:1084 upper -- O06 STATEMENT DEFECT, kernel-exhibited

`o06_convex_polygon_angle_sum` as frozen in `O06_ConvexPolygonAngleSum_SCAFFOLD.lean` is
FALSE, exactly as its own header warned: the hypotheses do not pin a cyclic order, and
`hcyclic` is VACUOUS because `EuclideanGeometry.angle` never exceeds `π`.

WITNESS: four DISTINCT COLLINEAR points listed out of order along the line -- 0, 2, 1, 3.
Every one of the four listed angles is `0`, so the sum is `0`, while `(h-2)π = 2π`.
The hull of a collinear set has empty interior, so it is its own frontier and `hfront`
holds for all four points. -/

def O06Statement : Prop :=
  ∀ (h : ℕ), 3 ≤ h → ∀ (p : ℕ → ℝ^ 2),
    p h = p 0 → p (h + 1) = p 1 →
    (∀ i, i < h → p i ∈ frontier (convexHull ℝ (Set.range p))) →
    (∀ i, i < h → ∀ j, j < h → p i = p j → i = j) →
    (∀ i, i < h → ∀ j, j < h →
      EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) ≤ Real.pi) →
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

noncomputable def Q : ℕ → ℝ^ 2
  | 0 => pt2 0 0
  | 1 => pt2 2 0
  | 2 => pt2 1 0
  | _ => pt2 3 0

noncomputable def pp (i : ℕ) : ℝ^ 2 := Q (i % 4)

noncomputable def LL : Submodule ℝ (ℝ^ 2) :=
  LinearMap.ker (EuclideanSpace.proj (1 : Fin 2)).toLinearMap

theorem hull_interior_empty (s : Set (ℝ^ 2)) (hs : s ⊆ (LL : Set (ℝ^ 2))) :
    interior (convexHull ℝ s) = ∅ := by
  have hsub : convexHull ℝ s ⊆ (LL : Set (ℝ^ 2)) := convexHull_min hs LL.convex
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hne : (interior (LL : Set (ℝ^ 2))).Nonempty := ⟨x, interior_mono hsub hx⟩
  have htop : LL = ⊤ := Submodule.eq_top_of_nonempty_interior' LL hne
  have hmem : (pt2 0 1) ∈ LL := by rw [htop]; trivial
  simp [LL, EuclideanSpace.proj, pt2] at hmem

theorem pp_mod (i : ℕ) : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega

theorem pp_range_sub : Set.range pp ⊆ {Q 0, Q 1, Q 2, Q 3} := by
  rintro x ⟨i, rfl⟩
  rcases pp_mod i with h | h | h | h <;> simp [pp, h]

theorem pp_range_finite : (Set.range pp).Finite :=
  Set.Finite.subset (Set.toFinite _) pp_range_sub

theorem pp_in_LL : Set.range pp ⊆ (LL : Set (ℝ^ 2)) := by
  rintro x ⟨i, rfl⟩
  rcases pp_mod i with h | h | h | h <;>
    simp [pp, h, Q, LL, EuclideanSpace.proj, pt2]

theorem pp_frontier (i : ℕ) : pp i ∈ frontier (convexHull ℝ (Set.range pp)) := by
  have hcl : IsClosed (convexHull ℝ (Set.range pp)) :=
    pp_range_finite.isClosed_convexHull (𝕜 := ℝ)
  rw [hcl.frontier_eq, hull_interior_empty _ pp_in_LL]
  exact ⟨subset_convexHull ℝ _ (Set.mem_range_self i), Set.notMem_empty _⟩

theorem o06_statement_false : ¬ O06Statement := by
  intro H
  have hper : pp 4 = pp 0 := by norm_num [pp]
  have hper' : pp 5 = pp 1 := by norm_num [pp]
  have hinj : ∀ i, i < 4 → ∀ j, j < 4 → pp i = pp j → i = j := by
    intro i hi j hj hEq
    interval_cases i <;> interval_cases j <;>
      first
        | rfl
        | (exfalso; simp only [pp, Q, pt2] at hEq
           have hc := congrArg (fun z => (WithLp.ofLp z) 0) hEq
           norm_num at hc)
  have hcyc : ∀ i, i < 4 → ∀ j, j < 4 →
      EuclideanGeometry.angle (pp i) (pp (i + 1)) (pp (i + 2)) ≤ Real.pi := by
    intro i _ j _
    exact EuclideanGeometry.angle_le_pi _ _ _
  have key := H 4 (by norm_num) pp hper hper' (fun i _ => pp_frontier i) hinj hcyc
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero] at key
  have a0 : EuclideanGeometry.angle (pp 0) (pp 1) (pp 2) = 0 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
    norm_num [pp, Q, pt2, EuclideanSpace.norm_eq, Fin.sum_univ_two, inner, vsub_eq_sub]
  have a1 : EuclideanGeometry.angle (pp 1) (pp 2) (pp 3) = 0 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
    norm_num [pp, Q, pt2, EuclideanSpace.norm_eq, Fin.sum_univ_two, inner, vsub_eq_sub]
  have a2 : EuclideanGeometry.angle (pp 2) (pp 3) (pp 4) = 0 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
    norm_num [pp, Q, pt2, EuclideanSpace.norm_eq, Fin.sum_univ_two, inner, vsub_eq_sub]
  have a3 : EuclideanGeometry.angle (pp 3) (pp 4) (pp 5) = 0 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
    norm_num [pp, Q, pt2, EuclideanSpace.norm_eq, Fin.sum_univ_two, inner, vsub_eq_sub]
  norm_num [a0, a1, a2, a3, Real.pi_ne_zero] at key

#print axioms o06_statement_false
