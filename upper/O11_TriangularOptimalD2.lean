import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 -- THE TARGET, ASSEMBLED

`erdos_1084.variants.triangular_optimal_d2`:  `f 2 (3k²+3k+1) = 9k²+3k`.

`f` here is the target's OWN `f`, reproduced verbatim, so this is the statement of
`FormalConjectures/ErdosProblems/1084.lean` and not a paraphrase.  The lower binder is
discharged by `Erdos1084.hex_lower` (KERNEL-SEALED, exit 0, 24.43 s, no `sorryAx`, no
`native_decide`) once its two Finset counts are proved for symbolic `k` (L01, L02); the
upper binder is O10.

STATUS: LADDER_ATTEMPT -- `le_antisymm`, nothing else.  The file compiles the moment its
two binders are supplied by their rungs.
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

theorem o11_triangular_optimal_d2 (k : ℕ)
    (hlow : 9 * k ^ 2 + 3 * k ≤ Erdos1084.f 2 (3 * k ^ 2 + 3 * k + 1))
    (hupp : Erdos1084.f 2 (3 * k ^ 2 + 3 * k + 1) ≤ 9 * k ^ 2 + 3 * k) :
    Erdos1084.f 2 (3 * k ^ 2 + 3 * k + 1) = 9 * k ^ 2 + 3 * k := le_antisymm hupp hlow
