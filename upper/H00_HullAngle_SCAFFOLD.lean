/-
H00_HullAngle_SCAFFOLD -- THE HULL-ANGLE DEVELOPMENT, architected (coordinator, 2026-09-05)

TARGET: discharge `o0406_hull_angle_package` (O05_DegreeSumBound.lean:294) — the last gap
of the O05 rung.  Coordinated with Contract C (session message, 2026-09-05 evening): the
coordinator owns this development; Contract C owns the hcentral m ≤ 3 residue of its own
line.  Everything here is stated against TODAY'S sealed assets:
  O04_SupportingLine.lean         (supporting functional at hull frontier, degenerate-aware)
  O02_CyclicAngularOrder_Repaired (the argument-sort enumeration pattern, wrap via shift)
  O06_InteriorPoint_EndToEnd      (InsideAngleAt + o06_angle_sum_of_interior_point)
  O06_FanAngleSum_UpperBound      (the ≤ direction, hypothesis-light)
  o03_udeg_le_six / o01_sixty     (O05_DegreeSumBound.lean, sealed)

THE REDUCTION (arithmetic, recorded here so nobody re-derives it): the existential `alpha`
is free upward, so the package holds iff  Σ_{v ∈ hullPts S} udeg S v ≤ 4h − 6  — take
`alpha v := (udeg v − 1)·π/3` and dump the slack on one vertex.  The aggregate bound is
what the angle machinery must deliver; the naive per-vertex `udeg ≤ 4` gives only `4h`
and provably loses by exactly the 6.

THE FOUR RUNGS (H1–H4), statement-first per campaign law.  A rung whose statement fails
to type-check is a defect to fix BEFORE any proof; a rung refuted by a kernel witness is
a FINDING to bank (twice today the frozen statement, not the prover, was wrong).

  H1 DEGENERATE: collinear S (hull interior empty) ⟹ every point has udeg ≤ 2 on the
     line, and Σ udeg ≤ 2h − 2 ≤ 4h − 6 directly.  No angles at all.
  H2 FULL TURN: v₀ ∈ interior(hull) and hull points sorted by argument about v₀ ⟹ every
     consecutive central gap < π, and the central angles sum to exactly 2π (telescope +
     wrap; the gap < π is where interior-ness enters: a gap ≥ π puts all vertices in a
     closed half-plane through v₀, contradicting interior).
  H3 INSIDE: for the sorted hull listing p about interior v₀, every i has
     `InsideAngleAt v₀ p i` — p(i), p(i+2) land on opposite sides of line(v₀, p(i+1))
     by sortedness (gaps < π from H2), and all three directions at p(i+1) fit in the
     supporting half-plane from O04.
  H4 CONE: at a hull vertex w, every unit-neighbour of w lies (from w) inside the hull
     cone at w, so O01's π/3 separation packs `udeg w ≤ 1 + 3·(interior angle at w)/π`.

ASSEMBLY: H2+H3 feed Contract C's `o06_angle_sum_of_interior_point` ⟹ Σ interior = (h−2)π;
H4 sums against it; H1 covers the empty-interior branch; the slack trick closes the
existential.  STATUS: SCAFFOLD — every rung `sorry`, every statement to be kernel
type-checked before proof work begins.
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

noncomputable def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

/-- `v` lies inside the angle at `p (i+1)` in polar form (VERBATIM from
`O06_InteriorPoint_EndToEnd.lean`, Contract C, sealed 2026-09-05). -/
def InsideAngleAt (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (i : ℕ) : Prop :=
  ∃ α β γ r₁ r₂ r₃ : ℝ,
    0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
    (p i).ofLp 0 = (p (i + 1)).ofLp 0 + r₁ * Real.cos α ∧
    (p i).ofLp 1 = (p (i + 1)).ofLp 1 + r₁ * Real.sin α ∧
    v.ofLp 0 = (p (i + 1)).ofLp 0 + r₂ * Real.cos β ∧
    v.ofLp 1 = (p (i + 1)).ofLp 1 + r₂ * Real.sin β ∧
    (p (i + 2)).ofLp 0 = (p (i + 1)).ofLp 0 + r₃ * Real.cos γ ∧
    (p (i + 2)).ofLp 1 = (p (i + 1)).ofLp 1 + r₃ * Real.sin γ ∧
    0 ≤ β - α ∧ β - α ≤ Real.pi ∧ 0 ≤ γ - β ∧ γ - β ≤ Real.pi ∧ γ - α ≤ Real.pi

/-! ## H1 — the degenerate branch: empty hull interior -/

/-- On a 1-separated set whose hull has empty interior (all points collinear), every
point has at most two unit-distance neighbours. -/
theorem h1_degenerate_udeg_le_two (S : Finset (ℝ^ 2))
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hdeg : interior (convexHull ℝ (S : Set (ℝ^ 2))) = ∅)
    (v : ℝ^ 2) (hv : v ∈ S) :
    udeg S v ≤ 2 := by
  sorry

/-! ## H2 — the full turn about an interior point, in POLAR-FAN form
(contract amended 2026-09-05 evening with Contract C: expose the sorted polar data the
construction already has — `a`, `r` with the gap bounds and the 2π telescope — matching
`o06_angle_sum_of_polar_fan` (O06_PolarFan_Handoff.lean, 8cee4a8593) exactly.  C then
derives hvne, hcentral and the ceiling itself; the winding-number reconstruction C's
falsifier flagged (67d0876128) dies unneeded.  Arguments INCREASE along the listing.) -/
theorem h2_full_turn (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h) (v₀ : ℝ^ 2)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ),
      (∀ i, p (i + h) = p i) ∧
      (∀ i < h, p i ∈ hullPts S) ∧
      (∀ w ∈ hullPts S, ∃ i < h, p i = w) ∧
      (∀ i, 0 < r i) ∧
      (∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i)) ∧
      (∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i)) ∧
      (∀ i < h, 0 ≤ a (i + 1) - a i) ∧
      (∀ i < h, a (i + 1) - a i ≤ Real.pi) ∧
      (∑ i ∈ Finset.range h, (a (i + 1) - a i) = 2 * Real.pi) := by
  sorry

/-! ## H3 — the interior point is inside every vertex angle (convexity-only under the
polar-fan contract; assigned to Contract C, statement kept here as the frozen socket) -/

theorem h3_inside_all (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h) (v₀ : ℝ^ 2)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))))
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hper : ∀ i, p (i + h) = p i)
    (hmem : ∀ i < h, p i ∈ hullPts S)
    (hsurj : ∀ w ∈ hullPts S, ∃ i < h, p i = w)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hnn : ∀ i < h, 0 ≤ a (i + 1) - a i)
    (hle : ∀ i < h, a (i + 1) - a i ≤ Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a (i + 1) - a i) = 2 * Real.pi) :
    ∀ i, InsideAngleAt v₀ p i := by
  sorry

/-! ## H4 — the cone bound at a hull vertex, against the listing's interior angle -/

theorem h4_cone_bound (S : Finset (ℝ^ 2)) (h : ℕ)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (p : ℕ → ℝ^ 2)
    (hper : ∀ i, p (i + h) = p i)
    (hmem : ∀ i < h, p i ∈ hullPts S)
    (hsurj : ∀ w ∈ hullPts S, ∃ i < h, p i = w)
    (i : ℕ) :
    (udeg S (p (i + 1)) : ℝ)
      ≤ 1 + 3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi := by
  sorry

/-! ## THE ASSEMBLY — the package from the four rungs (arithmetic + slack trick) -/

theorem hull_angle_package (S : Finset (ℝ^ 2)) (h : ℕ)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h) :
    ∃ alpha : ℝ^ 2 → ℝ,
      (∀ v ∈ hullPts S, (udeg S v : ℝ) ≤ 1 + 3 * alpha v / Real.pi) ∧
      (∑ v ∈ hullPts S, alpha v = ((h : ℝ) - 2) * Real.pi) := by
  sorry

end Erdos1084Upper

#print axioms Erdos1084Upper.hull_angle_package
