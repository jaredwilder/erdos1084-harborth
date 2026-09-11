import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O04, A SUPPORTING LINE AT A HULL POINT (SCAFFOLD)

A point of `S` on the boundary of the convex hull of `S` admits a supporting functional:
a nonzero continuous linear form `L` with `L u ≤ L v` for every `u ∈ S`.  Downstream this
is what confines the unit-distance neighbours of a hull vertex to a half-plane, and then
(with the polygon interior angle) to a cone.

The statement is deliberately written with a CONTINUOUS LINEAR FUNCTIONAL rather than an
inner product: it matches the shape Mathlib's Hahn-Banach separation actually produces,
and it avoids committing to the `inner` API, whose argument convention moved in 2025.

⛔ WHAT REMAINS, EXACTLY:
    instantiate `geometric_hahn_banach_point_closed` (or `geometric_hahn_banach_open`) at
    the convex set `convexHull ℝ ↑S` and the boundary point `v`, then convert the strict
    separation of an EXTERIOR point into the non-strict support at a FRONTIER point by a
    limiting argument over points outside the hull converging to `v` (`v ∈ frontier C`
    gives a sequence in `Cᶜ` tending to `v`), and extract a subsequential limit of the
    normalised functionals by compactness of the unit sphere in the 2-dimensional dual.
    Mathlib has the separation theorem; it does not package the frontier-support corollary.

STATUS: SCAFFOLD.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o04_supporting_line (S : Finset (ℝ^ 2)) (v : ℝ^ 2)
    (hv : v ∈ S) (hfr : v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ L : (ℝ^ 2) →L[ℝ] ℝ, L ≠ 0 ∧ ∀ u ∈ S, L u ≤ L v := by
  sorry
