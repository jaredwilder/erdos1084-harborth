import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O04, A SUPPORTING LINE AT A HULL POINT

A point of `S` on the boundary of the convex hull of `S` admits a supporting functional:
a nonzero continuous linear form `L` with `L u ≤ L v` for every `u ∈ S`.  Downstream this
is what confines the unit-distance neighbours of a hull vertex to a half-plane, and then
(with the polygon interior angle) to a cone.

The statement is deliberately written with a CONTINUOUS LINEAR FUNCTIONAL rather than an
inner product: it matches the shape Mathlib's Hahn-Banach separation actually produces,
and it avoids committing to the `inner` API, whose argument convention moved in 2025.

STATUS: CLOSED.  Statement UNCHANGED from `O04_SupportingLine_SCAFFOLD.lean`.

## HOW THE GAP CLOSED (and why the scaffold's plan was not needed)

The scaffold predicted a limiting argument over exterior points plus a compactness
extraction in the dual, on the belief that "Mathlib has the separation theorem; it does
not package the frontier-support corollary."  That belief is FALSE on this rev.  Mathlib
packages exactly the needed corollary:

    geometric_hahn_banach_of_nonempty_interior_point
      {A : Set E} (hA : Convex ℝ A) (hxA : x ∉ interior A) (hAint : (interior A).Nonempty) :
      ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ a ∈ A, f a ≤ f x
    (Mathlib/Analysis/LocallyConvex/Separation.lean; `StrongDual ℝ E` is an `abbrev`
     for `E →L[ℝ] ℝ`, so it unifies with the frozen statement's `L`.)

It already does the closure/limiting work internally (it separates `interior A` from `x`
and pushes the inequality back to `A` via `closure (interior A) = closure A`).  From
`v ∈ frontier C` we get exactly its hypothesis `v ∉ interior C`.

⛔ THE REAL GAP was elsewhere, and the scaffold did not name it: the Mathlib corollary
needs `(interior C).Nonempty`, which FAILS for degenerate `S` — a single point, or a
collinear `S`.  Those are not edge cases to wave at: for `#S ≤ 2`, or any collinear `S`,
`interior (convexHull ℝ ↑S) = ∅` while `frontier` is all of the hull, so `hfr` is
satisfiable and the theorem must still produce a nonzero `L`.  A proof that only ran
Hahn-Banach would be false-by-omission there.

The degenerate branch is handled on its own terms, and it does not need separation at all
(every `u ∈ S` gets `L u = L v`, not merely `≤`):

    interior (convexHull ℝ ↑S) = ∅
      → affineSpan ℝ ↑S ≠ ⊤            (interior_convexHull_nonempty_iff_affineSpan_eq_top)
      → vectorSpan ℝ ↑S ≠ ⊤            (affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty,
                                        legitimate since `v ∈ S` makes `↑S` nonempty)
      → (vectorSpan ℝ ↑S)ᗮ ≠ ⊥         (Submodule.orthogonal_eq_bot_iff, finite dimension)
      → pick `w ≠ 0` in the orthogonal complement and take `L := innerSL ℝ w`.
    Then `u - v ∈ vectorSpan ℝ ↑S` for every `u ∈ S`, so `L u - L v = ⟪w, u - v⟫ = 0`,
    and `L ≠ 0` because `L w = ⟪w, w⟫ ≠ 0`.

Nothing here is 2-dimension-specific; `ℝ^ 2` is only where the caller lives.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o04_supporting_line (S : Finset (ℝ^ 2)) (v : ℝ^ 2)
    (hv : v ∈ S) (hfr : v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ L : (ℝ^ 2) →L[ℝ] ℝ, L ≠ 0 ∧ ∀ u ∈ S, L u ≤ L v := by
  classical
  have hCconv : Convex ℝ (convexHull ℝ (S : Set (ℝ^ 2))) := convex_convexHull ℝ _
  have hSC : (S : Set (ℝ^ 2)) ⊆ convexHull ℝ (S : Set (ℝ^ 2)) := subset_convexHull ℝ _
  have hv' : v ∈ (S : Set (ℝ^ 2)) := Finset.mem_coe.mpr hv
  -- `frontier = closure \ interior`, so the hull point is not interior.
  have hvnot : v ∉ interior (convexHull ℝ (S : Set (ℝ^ 2))) := hfr.2
  by_cases hint : (interior (convexHull ℝ (S : Set (ℝ^ 2)))).Nonempty
  · -- NON-DEGENERATE: Mathlib's supporting-functional corollary applies verbatim.
    obtain ⟨f, hf0, hfle⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hCconv hvnot hint
    exact ⟨f, hf0, fun u hu => hfle u (hSC (Finset.mem_coe.mpr hu))⟩
  · -- DEGENERATE: the hull has empty interior, so `S` sits in a proper affine subspace
    -- and any normal to that subspace is a (constant, hence supporting) functional.
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
    refine ⟨innerSL ℝ w, ?_, ?_⟩
    · -- `L w = ⟪w, w⟫ ≠ 0`, so `L ≠ 0`.
      intro hL
      refine hw0 ?_
      have hww : (innerSL ℝ w) w = 0 := by rw [hL]; simp
      rw [innerSL_apply_apply] at hww
      exact inner_self_eq_zero.mp hww
    · -- `u - v` lies in the vector span, which `w` annihilates: `L u = L v`.
      intro u hu
      have hu' : u ∈ (S : Set (ℝ^ 2)) := Finset.mem_coe.mpr hu
      have hdiff : u - v ∈ vectorSpan ℝ (S : Set (ℝ^ 2)) := by
        have h1 := vsub_mem_vectorSpan (k := ℝ) (hp₁ := hu') (hp₂ := hv')
        simpa [vsub_eq_sub] using h1
      have hzero : (innerSL ℝ w) (u - v) = 0 := by
        rw [innerSL_apply_apply]
        exact (Submodule.mem_orthogonal' _ w).mp hwmem _ hdiff
      rw [map_sub] at hzero
      linarith

#print axioms o04_supporting_line
