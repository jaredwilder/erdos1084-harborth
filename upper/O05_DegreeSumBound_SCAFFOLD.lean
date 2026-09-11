import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O05, THE AGGREGATE DEGREE-SUM BOUND (SCAFFOLD)

`∑_{v ∈ S} deg v + 2h + 6 ≤ 6n`, i.e. the subtraction-free form of
`∑ deg ≤ 6n - 2h - 6`.  This is the single inequality the final assembly consumes, and
it is stated AGGREGATELY on purpose: the per-vertex peel needs a STRICTLY supporting
line (with a merely closed supporting half-plane the cone aperture can be exactly `π`,
which admits FOUR neighbours at `3 × 60°`, not three), and the aggregate form charges
that deficiency globally through the polygon angle sum instead.

⛔ WHAT REMAINS, EXACTLY:
    (1) interior vertices: `deg v ≤ 6`, which is O03 -- DONE (no sorry);
    (2) hull vertices: `deg v ≤ 1 + 3αᵥ/π` where `αᵥ` is the interior angle of the hull
        polygon at `v`, from O04's supporting line plus the same 60-degree gap argument
        run INSIDE a cone of aperture `αᵥ` rather than around a full turn;
    (3) `∑_{hull} αᵥ = (h-2)π`, which is O06 -- SCAFFOLD;
    (4) the arithmetic `∑ deg ≤ 6(n-h) + (h + 3(h-2)) = 6n - 2h - 6`, which is `linarith`
        once (1)-(3) are in hand, plus a `Nat`/`Real` cast discipline for the ℕ-valued
        degree sum against the ℝ-valued angle sum.
    (2) is the only genuinely new geometry; it is O03's pigeonhole with `2π` replaced by
    `αᵥ` and one extra neighbour permitted on the cone boundary.

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

theorem o05_degree_sum_bound (S : Finset (ℝ^ 2)) (n h : ℕ)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hn : n = S.card) (hh : h = (Erdos1084Upper.hullPts S).card) (h3 : 3 ≤ h) :
    (∑ v ∈ S, Erdos1084Upper.udeg S v) + 2 * h + 6 ≤ 6 * n := by
  sorry
