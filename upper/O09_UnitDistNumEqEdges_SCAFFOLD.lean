import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O09, THE COUNT BRIDGE (SCAFFOLD)

`unitDistNum S` (the target's noncomputable `Sym2`/`Quot.out` count) equals the edge count
of the unit-distance graph `UD S`, and the graph's degree at `v` equals `udeg S v`.  This
is the SAME bridge as `Erdos1084.unitDistNum_image` in the kernel-sealed lower-bound file,
which is why it is scoped small: that proof already exists and compiled.

⛔ WHAT REMAINS, EXACTLY:
    replay `unitDistNum_image`'s three steps with `Sym2.map (Subtype.val)` in place of
    `Sym2.map P`: (i) `Finset.card_bij` from the `p.out`-form filter to the
    `Sym2.lift ⟨dist, dist_comm⟩`-form filter (verbatim `lift_out` from the sealed file);
    (ii) `Finset.sym2_image` + injectivity of `Sym2.map Subtype.val`; (iii) identify the
    resulting filter with `SimpleGraph.edgeFinset` via `SimpleGraph.mem_edgeFinset` and
    `Sym2.ind`.  The degree half is `SimpleGraph.degree` = `#(neighborFinset)` and a
    `Finset.card_bij` against `nbrs S v` over the subtype coercion.
    NO NEW MATHEMATICS -- this is a transcription of a proof that is already kernel-sealed.

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

theorem o09_unitDistNum_eq_edges (S : Finset (ℝ^ 2)) :
    unitDistNum S = (Erdos1084Upper.UD S).edgeFinset.card ∧
      ∀ v : {x : ℝ^ 2 // x ∈ S},
        (Erdos1084Upper.UD S).degree v = Erdos1084Upper.udeg S (v : ℝ^ 2) := by
  sorry
