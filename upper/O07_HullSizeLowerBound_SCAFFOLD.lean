import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O07, THE HULL IS BIG (SCAFFOLD)

At `n = 3k² + 3k + 1` a 1-separated set has at least `6k` hull-boundary points.  This is
the packing/isoperimetric input, and it is what turns `e ≤ 3n - h - 3` into Harborth's
`e ≤ 3n - √(12n-3)`: `h ≥ √(12n-3) - 3 = 6k` exactly at the centred hexagonal numbers.

⛔ WHAT REMAINS, EXACTLY:
    the perimeter/area comparison.  Open discs of radius 1/2 around the points of `S` are
    pairwise disjoint (1-separation) and contained in `convexHull ↑S ⊕ B(0, 1/2)`, whose
    area is `A + P/2 + π/4` for hull area `A` and perimeter `P` (the Steiner formula for a
    convex body in the plane).  Consecutive hull vertices are `≥ 1` apart, so `P ≥ h`.
    The isoperimetric inequality `4πA ≤ P²` then gives `nπ/4 ≤ P²/(4π) + P/2 + π/4`, and
    with `P ≥ h` this bounds `h` from below by `√(12n-3) - 3` after algebra.
    ⛔ MATHLIB HAS NEITHER the planar Steiner formula NOR the isoperimetric inequality for
    convex bodies.  This rung is therefore the LARGEST remaining piece of the upper bound,
    larger than O02 ever was.  A CHEAPER SPECIALISED ROUTE MAY EXIST for `h ≥ 6k` only
    (a direct counting argument over the `2k+1` lattice rows of the hexagonal patch) and
    should be scoped before the general isoperimetric form is attempted.

STATUS: SCAFFOLD.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- The number of pairs of points of a finite set `s` in a metric space that are distance
1 apart.  (VERBATIM: FormalConjecturesForMathlib/Geometry/Metric.lean) -/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-- A set `s` is `≥ eps`-separated if its elements are pairwise at distance greater or
equal to `eps` from each other.
(VERBATIM: FormalConjecturesForMathlib/Topology/MetricSpace/MetricSeparated.lean) -/
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)

end Metric

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Erdos1084

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n`
1-separated points in `ℝ^d` make.
(VERBATIM: FormalConjectures/ErdosProblems/1084.lean) -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

end Erdos1084

namespace Erdos1084Upper

/-- The unit-distance neighbours of `v` inside `S`. -/
noncomputable def nbrs (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : Finset (ℝ^ 2) :=
  {u ∈ S | dist v u = 1}

/-- The unit-distance degree of `v` in `S`. -/
noncomputable def udeg (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : ℕ := (nbrs S v).card

/-- The unit-distance graph carried by `S`.  Loopless because `dist v v = 0 ≠ 1`. -/
def UD (S : Finset (ℝ^ 2)) : SimpleGraph {x : ℝ^ 2 // x ∈ S} where
  Adj u w := dist (u : ℝ^ 2) (w : ℝ^ 2) = 1
  symm := by
    intro u w h
    rw [dist_comm]
    exact h
  loopless := ⟨fun u h => by simp [dist_self] at h⟩

/-- The points of `S` on the boundary of its convex hull. -/
noncomputable def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

end Erdos1084Upper

theorem o07_hull_size_lower_bound (k : ℕ) (S : Finset (ℝ^ 2))
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hcard : S.card = 3 * k ^ 2 + 3 * k + 1) :
    6 * k ≤ (Erdos1084Upper.hullPts S).card := by
  sorry
