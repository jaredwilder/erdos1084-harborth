import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O02, THE CYCLIC ANGULAR ORDER (SCAFFOLD)

The assembled O2: the unit-distance neighbours of `v` admit a strictly increasing
enumeration of their polar arguments, extended by the wrap `a m = a 0 + 2π`, whose
consecutive gaps are each at least `π / 3` and sum to `2π`.

⛔ WHAT REMAINS, EXACTLY -- ONE ITEM, AND IT IS NOT A MISSING MATHLIB THEORY:
    the ENUMERATION PLUMBING.  Take `A : Finset ℝ` to be the image of `D` under the
    polar-argument map supplied by O02a; `Finset.orderIsoOfFin A rfl : Fin A.card ≃o A`
    IS IN MATHLIB and gives the strictly monotone listing.  What must still be written is
    (i) injectivity of the argument map on `D` (two distinct neighbours have distinct
    arguments, because equal arguments plus equal radius means equal point), so that
    `A.card = D.card`; (ii) the transport of that `Fin`-indexed order iso to a function
    `a : ℕ → ℝ` together with the wrap value at index `D.card`; and (iii) the consecutive
    gap bound, which is O01 (`π/3 ≤ angle`) chained through O02a + O02d + O02c
    (`angle ≤ |Δarg|`) -- both already written, both LADDER_ATTEMPT.
    The gap sum itself is O02e and is DONE.

CORRECTION TO THE CAMPAIGN REPORT (2026-09-02).  The report named O2 "THE BLOCKER, NOT IN
MATHLIB, 300-600 LOC".  After building it: the mathematical core is O02b
(`arccos (cos t) ≤ |t|`, four lines) and O02e (`Finset.sum_range_sub`, two lines), both
written.  The residue is bookkeeping over `Finset.orderIsoOfFin`.  MORE IMPORTANTLY: O03
does NOT need this file at all -- see O03_InteriorDegreeLeSix.lean, which reaches
`deg ≤ 6` by a PIGEONHOLE on six argument buckets and carries no `sorry`.  O2 is needed
only if a later rung wants the ORDER itself (O05's cone argument), not for O03.

STATUS: SCAFFOLD.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-- (VERBATIM: FormalConjecturesForMathlib/Topology/MetricSpace/MetricSeparated.lean) -/
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)

end Metric

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o02_cyclic_angular_order (v : ℝ^ 2) (D : Finset (ℝ^ 2))
    (hunit : ∀ u ∈ D, dist v u = 1)
    (hsep : ∀ u ∈ D, ∀ w ∈ D, u ≠ w → 1 ≤ dist u w) :
    ∃ a : ℕ → ℝ,
      (∀ i, i < D.card → -Real.pi < a i ∧ a i ≤ Real.pi) ∧
      (∀ i, i + 1 < D.card → a i < a (i + 1)) ∧
      a D.card = a 0 + 2 * Real.pi ∧
      (∀ i, i < D.card → Real.pi / 3 ≤ a (i + 1) - a i) ∧
      ∑ i ∈ Finset.range D.card, (a (i + 1) - a i) = 2 * Real.pi := by
  sorry
