import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry Finset

/-! # erdos:1084 upper -- H3, THE DECOMPOSITION, statement-first.

Rung H3 of the hull-angle package is this session's under the agreed division. This file
freezes the decomposition and type-checks it BEFORE any proof is attempted, per campaign
law. Two sub-obligations, each a real theorem, each named.

⛔ WHAT THE PROBES ALREADY SETTLED (receipts beside this file):

* `h3_sortedness_falsifier*.py` -- H3's ORIGINAL hypotheses never stated that the listing
  is in cyclic order, and `InsideAngleAt` is false without it. Exhaustive over every
  permutation of regular h-gons h = 4..8 and over 3,984 irregular configurations: no
  scrambled listing satisfies them, so they DO force the order -- by a winding argument
  nobody had written. The producing rung now hands the sorted polar data over instead, so
  that argument is not needed.
* `h3probe3.py` -- SORTED POLAR DATA ABOUT `v₀` IS NOT ENOUGH ON ITS OWN. Of 11,258
  configurations with arguments sorted about `v₀` and every central gap `< π`, 7,215 FAIL
  `InsideAngleAt`. Every one of them has a listed point that is NOT a hull point. So the
  `hmem` hypothesis (every listed point lies on the hull frontier) is LOAD-BEARING and no
  proof may run without it.
* `h3probe4.py` -- with hull vertices only and `v₀` strictly interior, 30,000 honest
  configurations, ZERO failures.

THE DECOMPOSITION. `v₀` lies inside the angle at `p (i+1)` exactly when it is strictly on
the same side of the line through `p (i+1)` and `p i` as `p (i+2)`, and strictly on the
same side of the line through `p (i+1)` and `p (i+2)` as `p i`. The first pair of facts is
CONVEXITY (consecutive hull points span a supporting line, and an interior point is
strictly inside it); the second step is the conversion of those side conditions into the
polar form `InsideAngleAt` is written in.
-/

/-- VERBATIM from `O06_InteriorPoint_EndToEnd.lean` and `H00_HullAngle_SCAFFOLD.lean`. -/
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

/-- The planar cross product of `b - a` and `c - a`. Positive means `c` is strictly to the
left of the directed line `a → b`. -/
noncomputable def cross (a b c : ℝ^ 2) : ℝ :=
  (b.ofLp 0 - a.ofLp 0) * (c.ofLp 1 - a.ofLp 1)
    - (b.ofLp 1 - a.ofLp 1) * (c.ofLp 0 - a.ofLp 0)

/-! ## S1 -- CONVEXITY. Consecutive hull points span a supporting line. -/

/-- ⛔ OBLIGATION S1. For a listing of hull points sorted by argument about an interior
point `v₀`, consecutive entries span a hull EDGE, so the line through them supports the
hull and `v₀`, being interior, is STRICTLY on one side; the next vertex is on that same
side. This is the whole geometric content of H3 and it is the recon map's
`geometric_hahn_banach_open_point` route. -/
theorem s1_consecutive_supporting (S : Finset (ℝ^ 2)) (h : ℕ) (v₀ : ℝ^ 2)
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))))
    (hmem : ∀ i < h, p i ∈ S ∧ p i ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2))))
    (hsurj : ∀ w ∈ S, w ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2))) → ∃ i < h, p i = w)
    (hper : ∀ i, p (i + h) = p i)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hnn : ∀ i, i < h → 0 ≤ a (i + 1) - a i)
    (hle : ∀ i, i < h → a (i + 1) - a i ≤ Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a (i + 1) - a i) = 2 * Real.pi)
    (i : ℕ) :
    0 < cross (p (i + 1)) (p i) v₀ * cross (p (i + 1)) (p i) (p (i + 2)) ∧
    0 < cross (p (i + 1)) (p (i + 2)) v₀ * cross (p (i + 1)) (p (i + 2)) (p i) := by
  sorry

/-! ## S2 -- CONVERSION. Two strict side conditions give the polar form. -/

/-- ⛔ OBLIGATION S2. If `v` is strictly on the same side of the line `Y → X` as `Z`, and
strictly on the same side of `Y → Z` as `X`, then `v` lies in the open cone at `Y` and the
three polar arguments about `Y` order with both arcs and the total arc at most `π`. This is
pure plane trigonometry: no hull, no convexity. -/
theorem s2_sides_to_polar (v X Y Z : ℝ^ 2)
    (hXY : X ≠ Y) (hZY : Z ≠ Y) (hvY : v ≠ Y)
    (h1 : 0 < cross Y X v * cross Y X Z)
    (h2 : 0 < cross Y Z v * cross Y Z X)
    (p : ℕ → ℝ^ 2) (i : ℕ) (hpi : p i = X) (hpi1 : p (i + 1) = Y) (hpi2 : p (i + 2) = Z) :
    InsideAngleAt v p i := by
  sorry

/-! ## H3, assembled from S1 and S2. -/

theorem h3_from_S1_S2 (S : Finset (ℝ^ 2)) (h : ℕ) (v₀ : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (hS1 : ∀ i,
      0 < cross (p (i + 1)) (p i) v₀ * cross (p (i + 1)) (p i) (p (i + 2)) ∧
      0 < cross (p (i + 1)) (p (i + 2)) v₀ * cross (p (i + 1)) (p (i + 2)) (p i))
    (hne1 : ∀ i, p i ≠ p (i + 1)) (hne2 : ∀ i, p (i + 2) ≠ p (i + 1))
    (hnev : ∀ i, v₀ ≠ p (i + 1)) :
    ∀ i, InsideAngleAt v₀ p i := by
  intro i
  exact s2_sides_to_polar v₀ (p i) (p (i + 1)) (p (i + 2)) (hne1 i) (hne2 i) (hnev i)
    (hS1 i).1 (hS1 i).2 p i rfl rfl rfl

/-! ## ⛔ STATEMENT DEFECT IN THIS FILE'S OWN FIRST DRAFT, FOUND AND REPAIRED 2026-09-05.

S2 was first frozen with the side conditions written as IFFs
(`0 < cross Y X v ↔ 0 < cross Y X Z`). An iff holds VACUOUSLY when both sides are false,
and every cross product vanishes on a collinear configuration, so that S2 asserted
`InsideAngleAt` for `X = (1,0)`, `Y = 0`, `Z = (2,0)`, `v = (-1,0)` -- where the polar
constraints force `γ - α = 2π > π`. KERNEL REFUTATION:
`O06_S2_Refutation.lean`, `s2_statement_false`, clean triple.

The hypotheses above are the repair: STRICTLY the same side is a positive PRODUCT, never an
iff. Falsifier on the repaired form: 123,045 configurations satisfying it, ZERO
`InsideAngleAt` failures (`s2_repaired_falsifier.py`).
-/
