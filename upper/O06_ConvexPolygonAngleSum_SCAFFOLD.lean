import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O06, THE CONVEX POLYGON INTERIOR-ANGLE SUM (SCAFFOLD)

`∑ interior angles = (h - 2)π` for a convex `h`-gon listed in cyclic order.

⛔ WHAT REMAINS, EXACTLY -- AND THE FIRST ITEM IS THE REAL COST:
    (a) Mathlib HAS NO PREDICATE "these points are the vertices of a convex polygon in
        cyclic order".  The hypotheses below (periodicity, frontier membership,
        injectivity on `range h`) are a HONEST APPROXIMATION and are almost certainly not
        strong enough on their own -- they do not forbid a cyclic RE-ORDERING of the
        vertices, and the angle sum is false for a re-ordered listing.  The correct
        hypothesis is a cyclic ORDER condition (each `p (i+1)` is the next vertex
        anticlockwise), which is O02's machinery applied to the hull vertices seen from
        an interior point.  THIS IS WHY O02 IS STILL WANTED even though O03 does not need
        it.
    (b) with a correct cyclic-order hypothesis, the sum is an induction on `h` via
        `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` (the triangle angle sum,
        WHICH MATHLIB HAS) along a fan triangulation from `p 0`.
    ⛔ DO NOT WEAKEN THE STATEMENT TO MAKE IT PROVABLE.  A polygon angle sum proved under
    hypotheses that do not pin the cyclic order is a true theorem about nothing.

STATUS: SCAFFOLD.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o06_convex_polygon_angle_sum (h : ℕ) (hh : 3 ≤ h) (p : ℕ → ℝ^ 2)
    (hper : p h = p 0) (hper' : p (h + 1) = p 1)
    (hfront : ∀ i, i < h → p i ∈ frontier (convexHull ℝ (Set.range p)))
    (hinj : ∀ i, i < h → ∀ j, j < h → p i = p j → i = j)
    (hcyclic : ∀ i, i < h → ∀ j, j < h →
      EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) ≤ Real.pi) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi := by
  sorry
