/-
H04_ConeBound -- rung H4 of the hull-angle development (sub-agent, 2026-09-05)

FROZEN TARGET: `h4_cone_bound`, byte-identical to `H00_HullAngle_SCAFFOLD.lean:131-141`.

STATUS: see the ⛔ block above the frozen statement.  The two HALVES of the rung are
SEALED here as independent, reusable lemmas (this is the PARTIAL shape the mission named);
the JOIN is not sorried for lack of effort -- the frozen statement is REFUTED.

  SEALED  `h4_packing`             the π/3 packing, abstracted: k values in an interval of
                                   length (b-a), pairwise ≥ d apart, force k ≤ 1 + (b-a)/d.
  SEALED  `h4_halfplane_theta`     the cone-containment half at O04 strength: at a hull
                                   point the argument function of every unit neighbour is
                                   confined to an interval of length π (a closed half-plane).
  SEALED  `h4_cone_packing`        the two halves joined at a PARAMETRIC aperture: this is
                                   exactly `udeg w ≤ 1 + 3·alpha/π` once `alpha` is supplied
                                   as a genuine cone containing the neighbours.  It is the
                                   shape H4 was reaching for, and it is DONE.
  SEALED  `h4_hull_udeg_le_four`   `h4_cone_packing` at alpha = π: every hull point of a
                                   1-separated set has unit-degree ≤ 4 (vs the global 6 of
                                   `o03_udeg_le_six`).  New; O05 asserted it, nobody had it.
  SEALED  `h4_hull_degree_sum_le`  its aggregate form `Σ_{hull} udeg ≤ 4h`.  O05 needs
                                   `4h - 6`; this is that bound minus exactly the 6, which
                                   `H00`'s own header predicted would be the residue.
  SEALED  `notMem_interior_of_le` / `mem_frontier_of_le`   the CONVERSE of O04: a maximiser
                                   of a nonzero functional over `S` is ON the hull frontier.
                                   Mathlib packages only the direction O04 uses.
  ⛔ REFUTED `h4_cone_bound`        two independent kernel witnesses, both `h = 4`:
                                   `h4_cone_bound_false` (collinear `S`) and
                                   `h4_cone_bound_false_nondegenerate` (a strictly convex
                                   quadrilateral -- so NON-DEGENERACY IS NOT THE FIX).
                                   Missing hypothesis: the CYCLIC ORDER of `p`.

REUSED VERBATIM from sealed files (clean triples on this rev): `o01_sixty`,
`abs_toReal_coe_le` (O05_DegreeSumBound.lean) and `o04_supporting_line`
(O04_SupportingLine.lean).  `h4_halfplane_theta`'s gap clause is `o02_argument_function`'s
proof re-run against a CHOSEN reference vector (the inward normal of the supporting line)
instead of a basis vector -- that single change is what buys the interval bound.

Mathlib pinned 919544d4 / v4.31.0-rc1.
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

/-! ## REUSED SEALED ASSETS (verbatim) -/

/-- VERBATIM `o01_sixty`, `O05_DegreeSumBound.lean` (SEALED, clean triple). -/
theorem o01_sixty : ∀ p q r : ℝ^ 2, dist p q = 1 → dist p r = 1 → 1 ≤ dist q r →
    Real.pi / 3 ≤ EuclideanGeometry.angle q p r := by
  intro p q r hq hr hqr
  have hlaw := EuclideanGeometry.law_cos q p r
  rw [dist_comm q p, dist_comm r p, hq, hr] at hlaw
  have hsq : (1 : ℝ) ≤ dist q r * dist q r := by nlinarith [hqr]
  have hcos : Real.cos (EuclideanGeometry.angle q p r) ≤ 1 / 2 := by linarith
  by_contra hcon
  push_neg at hcon
  have h0 : 0 ≤ EuclideanGeometry.angle q p r := EuclideanGeometry.angle_nonneg q p r
  have hle : EuclideanGeometry.angle q p r ≤ Real.pi := EuclideanGeometry.angle_le_pi q p r
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlt : Real.cos (Real.pi / 3) < Real.cos (EuclideanGeometry.angle q p r) :=
    Real.strictAntiOn_cos ⟨h0, hle⟩ ⟨by positivity, by linarith⟩ hcon
  rw [Real.cos_pi_div_three] at hlt
  linarith

/-- VERBATIM `abs_toReal_coe_le`, `O05_DegreeSumBound.lean` (SEALED, clean triple). -/
theorem abs_toReal_coe_le (t : ℝ) : |Real.Angle.toReal (t : Real.Angle)| ≤ |t| := by
  have hb : |Real.Angle.toReal (t : Real.Angle)| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.Angle.neg_pi_lt_toReal _), Real.Angle.toReal_le_pi _⟩
  by_cases hc : -Real.pi < t ∧ t ≤ Real.pi
  · rw [Real.Angle.toReal_coe_eq_self_iff.mpr hc]
  · push_neg at hc
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hge : Real.pi ≤ |t| := by
      rcases le_or_gt t (-Real.pi) with h1 | h1
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have h2 : Real.pi < t := hc h1
        rw [abs_of_nonneg (by linarith)]; linarith
    linarith

/-- VERBATIM `o04_supporting_line`, `O04_SupportingLine.lean` (SEALED, clean triple). -/
theorem o04_supporting_line (S : Finset (ℝ^ 2)) (v : ℝ^ 2)
    (hv : v ∈ S) (hfr : v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ L : (ℝ^ 2) →L[ℝ] ℝ, L ≠ 0 ∧ ∀ u ∈ S, L u ≤ L v := by
  classical
  have hCconv : Convex ℝ (convexHull ℝ (S : Set (ℝ^ 2))) := convex_convexHull ℝ _
  have hSC : (S : Set (ℝ^ 2)) ⊆ convexHull ℝ (S : Set (ℝ^ 2)) := subset_convexHull ℝ _
  have hv' : v ∈ (S : Set (ℝ^ 2)) := Finset.mem_coe.mpr hv
  have hvnot : v ∉ interior (convexHull ℝ (S : Set (ℝ^ 2))) := hfr.2
  by_cases hint : (interior (convexHull ℝ (S : Set (ℝ^ 2)))).Nonempty
  · obtain ⟨f, hf0, hfle⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hCconv hvnot hint
    exact ⟨f, hf0, fun u hu => hfle u (hSC (Finset.mem_coe.mpr hu))⟩
  · have hspanS : affineSpan ℝ (S : Set (ℝ^ 2)) ≠ ⊤ := fun h =>
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
    · intro hL
      refine hw0 ?_
      have hww : (innerSL ℝ w) w = 0 := by rw [hL]; simp
      rw [innerSL_apply_apply] at hww
      exact inner_self_eq_zero.mp hww
    · intro u hu
      have hu' : u ∈ (S : Set (ℝ^ 2)) := Finset.mem_coe.mpr hu
      have hdiff : u - v ∈ vectorSpan ℝ (S : Set (ℝ^ 2)) := by
        have h1 := vsub_mem_vectorSpan (k := ℝ) (hp₁ := hu') (hp₂ := hv')
        simpa [vsub_eq_sub] using h1
      have hzero : (innerSL ℝ w) (u - v) = 0 := by
        rw [innerSL_apply_apply]
        exact (Submodule.mem_orthogonal' _ w).mp hwmem _ hdiff
      rw [map_sub] at hzero
      linarith

namespace Erdos1084Upper

/-! ## H00 DEFINITIONS (verbatim) -/

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

/-! ## HALF ONE -- THE π/3 PACKING, abstracted off the geometry entirely.

`k` points whose `theta`-values lie in `[a, b]` and are pairwise at least `d` apart force
`k ≤ 1 + (b-a)/d`.  Proved by the O03 device (an injective floor-bucket map into a
`Finset.range`), not by sorting: no `LinearOrder` on the index type is required, and the
empty case needs no separate branch. -/

theorem h4_packing {α : Type*} (T : Finset α) (theta : α → ℝ) (d a b : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hpair : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → d ≤ |theta x - theta y|)
    (hlo : ∀ x ∈ T, a ≤ theta x) (hhi : ∀ x ∈ T, theta x ≤ b) :
    (T.card : ℝ) ≤ 1 + (b - a) / d := by
  classical
  have hBA : (0 : ℝ) ≤ (b - a) / d := div_nonneg (by linarith) hd.le
  have hNfloor : (0 : ℤ) ≤ ⌊(b - a) / d⌋ := Int.floor_nonneg.mpr hBA
  have hNle : (((⌊(b - a) / d⌋).toNat : ℕ) : ℝ) ≤ (b - a) / d := by
    have h1 : (((⌊(b - a) / d⌋).toNat : ℤ) : ℝ) ≤ (b - a) / d := by
      rw [Int.toNat_of_nonneg hNfloor]
      exact Int.floor_le _
    exact_mod_cast h1
  have hmapsto : Set.MapsTo (fun x => (⌊(theta x - a) / d⌋).toNat)
      (↑T : Set α) (↑(Finset.range ((⌊(b - a) / d⌋).toNat + 1)) : Set ℕ) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_coe, Finset.mem_range]
    have h1 : (0 : ℝ) ≤ (theta x - a) / d := div_nonneg (by linarith [hlo x hx]) hd.le
    have h2 : (theta x - a) / d ≤ (b - a) / d := by
      have hkey : (b - a) / d - (theta x - a) / d = (b - theta x) / d := by
        first
          | (rw [div_sub_div_same]; ring_nf)
          | (field_simp; ring)
      have hpos : (0 : ℝ) ≤ (b - theta x) / d := div_nonneg (by linarith [hhi x hx]) hd.le
      linarith
    have hf1 : (0 : ℤ) ≤ ⌊(theta x - a) / d⌋ := Int.floor_nonneg.mpr h1
    have hf2 : ⌊(theta x - a) / d⌋ ≤ ⌊(b - a) / d⌋ := Int.floor_le_floor h2
    show (⌊(theta x - a) / d⌋).toNat < (⌊(b - a) / d⌋).toNat + 1
    omega
  have hinj : Set.InjOn (fun x => (⌊(theta x - a) / d⌋).toNat) (↑T : Set α) := by
    intro x hx y hy hf
    rw [Finset.mem_coe] at hx hy
    by_contra hxy
    have hdxy := hpair x hx y hy hxy
    have hf' : (⌊(theta x - a) / d⌋).toNat = (⌊(theta y - a) / d⌋).toNat := hf
    have h1 : (0 : ℝ) ≤ (theta x - a) / d := div_nonneg (by linarith [hlo x hx]) hd.le
    have h2 : (0 : ℝ) ≤ (theta y - a) / d := div_nonneg (by linarith [hlo y hy]) hd.le
    have hf1 : (0 : ℤ) ≤ ⌊(theta x - a) / d⌋ := Int.floor_nonneg.mpr h1
    have hf2 : (0 : ℤ) ≤ ⌊(theta y - a) / d⌋ := Int.floor_nonneg.mpr h2
    have hfeq : ⌊(theta x - a) / d⌋ = ⌊(theta y - a) / d⌋ := by omega
    have hA1 := Int.floor_le ((theta x - a) / d)
    have hA2 := Int.lt_floor_add_one ((theta x - a) / d)
    have hB1 := Int.floor_le ((theta y - a) / d)
    have hB2 := Int.lt_floor_add_one ((theta y - a) / d)
    rw [hfeq] at hA1 hA2
    have habs : |(theta x - a) / d - (theta y - a) / d| < 1 := by
      rw [abs_sub_lt_iff]; constructor <;> linarith
    have heq : (theta x - a) / d - (theta y - a) / d = (theta x - theta y) / d := by
      first
        | (rw [div_sub_div_same]; ring_nf)
        | (field_simp; ring)
    rw [heq, abs_div, abs_of_pos hd] at habs
    first
      | rw [div_lt_one hd] at habs
      | rw [div_lt_one₀ hd] at habs
    linarith
  have hcard : T.card ≤ (Finset.range ((⌊(b - a) / d⌋).toNat + 1)).card :=
    Finset.card_le_card_of_injOn _ hmapsto hinj
  rw [Finset.card_range] at hcard
  have hR : (T.card : ℝ) ≤ (((⌊(b - a) / d⌋).toNat : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  linarith

/-! ## HALF TWO -- THE CONE CONTAINMENT, at the strength O04 actually delivers.

At a point of `S` on the hull frontier there is an argument function whose values on the
unit neighbours are confined to `[-π/2, π/2]` -- an interval of length exactly `π`, the
aperture of the closed supporting half-plane.  Construction: `o04_supporting_line` gives a
supporting functional `L`; Riesz turns `-L` into the INWARD normal `n`; the argument is
measured FROM `n`, and `⟪n, u - w⟫ ≥ 0` caps the angle at `π/2`. -/

theorem h4_halfplane_theta (S : Finset (ℝ^ 2)) (w : ℝ^ 2)
    (hw : w ∈ S) (hfr : w ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ theta : ℝ^ 2 → ℝ,
      (∀ u ∈ S, ∀ z ∈ S, dist w u = 1 → dist w z = 1 →
        EuclideanGeometry.angle u w z ≤ |theta u - theta z|) ∧
      (∀ u ∈ S, dist w u = 1 → -(Real.pi / 2) ≤ theta u) ∧
      (∀ u ∈ S, dist w u = 1 → theta u ≤ Real.pi / 2) := by
  classical
  haveI : Fact (Module.finrank ℝ (ℝ^ 2) = 2) := ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨L, hL0, hLle⟩ := o04_supporting_line S w hw hfr
  have hL'0 : (-L) ≠ 0 := neg_ne_zero.mpr hL0
  obtain ⟨n, hnapp⟩ : ∃ n : ℝ^ 2, ∀ x : ℝ^ 2, inner ℝ n x = (-L) x :=
    ⟨(InnerProductSpace.toDual ℝ (ℝ^ 2)).symm (-L),
      fun _ => InnerProductSpace.toDual_symm_apply⟩
  have hn0 : n ≠ 0 := by
    intro hz
    refine hL'0 (ContinuousLinearMap.ext (fun x => ?_))
    have hx := hnapp x
    rw [hz, inner_zero_left] at hx
    simpa using hx.symm
  have hnonneg : ∀ u ∈ S, 0 ≤ inner ℝ n (u - w) := by
    intro u hu
    rw [hnapp]
    simp only [ContinuousLinearMap.neg_apply, map_sub]
    have hle := hLle u hu
    linarith
  have hB := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hbound : ∀ u ∈ S, dist w u = 1 →
      |(hB.orientation.oangle n (u - w)).toReal| ≤ Real.pi / 2 := by
    intro u hu hdu
    have hune : u - w ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0, dist_self] at hdu
      norm_num at hdu
    have heq : InnerProductGeometry.angle n (u - w)
        = |(hB.orientation.oangle n (u - w)).toReal| :=
      Orientation.angle_eq_abs_oangle_toReal hB.orientation hn0 hune
    rw [← heq]
    have hcos : 0 ≤ Real.cos (InnerProductGeometry.angle n (u - w)) := by
      rw [InnerProductGeometry.cos_angle]
      exact div_nonneg (hnonneg u hu) (by positivity)
    by_contra hcon
    push_neg at hcon
    have h2 : InnerProductGeometry.angle n (u - w) ≤ Real.pi :=
      InnerProductGeometry.angle_le_pi _ _
    have h3 := Real.cos_neg_of_pi_div_two_lt_of_lt hcon (by linarith [Real.pi_pos])
    linarith
  refine ⟨fun x => (hB.orientation.oangle n (x - w)).toReal, ?_, ?_, ?_⟩
  · intro u hu z hz hdu hdz
    try dsimp only
    have hune : u - w ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0, dist_self] at hdu
      norm_num at hdu
    have hzne : z - w ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0, dist_self] at hdz
      norm_num at hdz
    have hdef : EuclideanGeometry.angle u w z
        = InnerProductGeometry.angle (u - w) (z - w) := rfl
    have hangle : EuclideanGeometry.angle u w z
        = |(hB.orientation.oangle (u - w) (z - w)).toReal| := by
      rw [hdef, Orientation.angle_eq_abs_oangle_toReal hB.orientation hune hzne]
    have hadd := Orientation.oangle_add hB.orientation hn0 hune hzne
    have hsub : hB.orientation.oangle (u - w) (z - w)
        = hB.orientation.oangle n (z - w) - hB.orientation.oangle n (u - w) := by
      rw [← hadd]; abel
    have hAB : hB.orientation.oangle n (z - w) - hB.orientation.oangle n (u - w)
        = ((((hB.orientation.oangle n (z - w)).toReal
            - (hB.orientation.oangle n (u - w)).toReal : ℝ)) : Real.Angle) := by
      rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    rw [hangle, hsub, hAB]
    refine le_trans (abs_toReal_coe_le _) ?_
    first
      | rw [abs_sub_comm]
      | exact le_of_eq (abs_sub_comm _ _)
  · intro u hu hdu
    exact (abs_le.mp (hbound u hu hdu)).1
  · intro u hu hdu
    exact (abs_le.mp (hbound u hu hdu)).2

/-! ## THE JOIN AT A PARAMETRIC APERTURE -- this is the true H4.

Supply ANY argument function whose unit-neighbour values sit in an interval of length
`alpha`, and the O01 sixty-degree spacing closes the bound.  The frozen H4 is the special
case where `alpha` is the hull's interior angle at the vertex; `h4_hull_udeg_le_four` below
is the special case `alpha = π` that the supporting line delivers unconditionally. -/

theorem h4_cone_packing (S : Finset (ℝ^ 2)) (w : ℝ^ 2) (a alpha : ℝ)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2))) (halpha : 0 ≤ alpha)
    (theta : ℝ^ 2 → ℝ)
    (hgap : ∀ u ∈ S, ∀ z ∈ S, dist w u = 1 → dist w z = 1 →
      EuclideanGeometry.angle u w z ≤ |theta u - theta z|)
    (hlo : ∀ u ∈ S, dist w u = 1 → a ≤ theta u)
    (hhi : ∀ u ∈ S, dist w u = 1 → theta u ≤ a + alpha) :
    (udeg S w : ℝ) ≤ 1 + 3 * alpha / Real.pi := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have hsepP : (S : Set (ℝ^ 2)).Pairwise (fun p q => (1 : ℝ≥0∞) ≤ edist p q) := hsep
  have hcardT : udeg S w = (S.filter (fun u => dist w u = 1)).card := by
    first
      | rfl
      | simp [udeg, nbrs]
  have hpair : ∀ x ∈ S.filter (fun u => dist w u = 1),
      ∀ y ∈ S.filter (fun u => dist w u = 1), x ≠ y → Real.pi / 3 ≤ |theta x - theta y| := by
    intro x hx y hy hxy
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hxd : dist w x = 1 := (Finset.mem_filter.mp hx).2
    have hyd : dist w y = 1 := (Finset.mem_filter.mp hy).2
    have hdxy : (1 : ℝ) ≤ dist x y := by
      have he : (1 : ℝ≥0∞) ≤ edist x y :=
        hsepP (Finset.mem_coe.mpr hxS) (Finset.mem_coe.mpr hyS) hxy
      rw [edist_dist] at he
      exact ENNReal.one_le_ofReal.mp he
    exact le_trans (o01_sixty w x y hxd hyd hdxy) (hgap x hxS y hyS hxd hyd)
  have hlo' : ∀ x ∈ S.filter (fun u => dist w u = 1), a ≤ theta x := fun x hx =>
    hlo x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hhi' : ∀ x ∈ S.filter (fun u => dist w u = 1), theta x ≤ a + alpha := fun x hx =>
    hhi x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hkey := h4_packing (S.filter (fun u => dist w u = 1)) theta (Real.pi / 3) a (a + alpha)
    (by positivity) (by linarith) hpair hlo' hhi'
  have harith : (a + alpha - a) / (Real.pi / 3) = 3 * alpha / Real.pi := by
    field_simp
    ring
  rw [harith] at hkey
  rw [hcardT]
  exact hkey

/-! ## THE UNCONDITIONAL HULL BOUND -- `udeg ≤ 4` on the frontier (new). -/

theorem h4_hull_udeg_le_four (S : Finset (ℝ^ 2)) (w : ℝ^ 2)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hw : w ∈ S) (hfr : w ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))) :
    udeg S w ≤ 4 := by
  obtain ⟨theta, hgap, hlo, hhi⟩ := h4_halfplane_theta S w hw hfr
  have hhi' : ∀ u ∈ S, dist w u = 1 → theta u ≤ -(Real.pi / 2) + Real.pi := by
    intro u hu hdu
    have := hhi u hu hdu
    linarith
  have hkey := h4_cone_packing S w (-(Real.pi / 2)) Real.pi hsep Real.pi_pos.le theta hgap
    hlo hhi'
  have hR : (udeg S w : ℝ) ≤ 4 := by
    have h3 : 3 * Real.pi / Real.pi = 3 := by
      field_simp
    rw [h3] at hkey
    linarith
  exact_mod_cast hR

theorem h4_hull_udeg_le_four' (S : Finset (ℝ^ 2)) (w : ℝ^ 2)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2))) (hw : w ∈ hullPts S) :
    udeg S w ≤ 4 :=
  h4_hull_udeg_le_four S w hsep (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2

/-- The aggregate form.  O05's assembly needs `Σ_{hull} udeg ≤ 4h - 6`; this is that bound
short by exactly the `6`, which is the residue `H00`'s header predicted. -/
theorem h4_hull_degree_sum_le (S : Finset (ℝ^ 2)) (h : ℕ)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2))) (hh : h = (hullPts S).card) :
    (∑ v ∈ hullPts S, udeg S v) ≤ 4 * h := by
  calc (∑ v ∈ hullPts S, udeg S v)
      ≤ ∑ _v ∈ hullPts S, 4 :=
        Finset.sum_le_sum (fun v hv => h4_hull_udeg_le_four' S v hsep hv)
    _ = 4 * h := by rw [Finset.sum_const, smul_eq_mul, mul_comm, hh]

/-! ## H4 -- THE FROZEN STATEMENT.

⛔ REFUTED, NOT MERELY OPEN.  The hypotheses `hper / hmem / hsurj` make `p` an arbitrary
bijection `ℤ/h → hullPts S`; NOTHING pins the CYCLIC ORDER.  `p i` and `p (i+2)` are
therefore two arbitrary hull points, and `∠ (p i) (p (i+1)) (p (i+2))` is not the interior
angle at `p (i+1)` -- it can be made as small as one likes while `udeg (p (i+1))` stays 2.
H3's signature carries `v₀ / hne / hgap / hcentral`, which is exactly what encodes the
order; H4 was written by DELETING those binders, and the statement fell with them.

TWO independent witnesses, both with `h = 4`:

  (a) COLLINEAR (formalised as `h4_cone_bound_false` below).
      `S = {(0,0), (2,0), (1,0), (3,0)}`, all four on the frontier because a collinear
      hull has empty interior.  Listing `p = (0,0), (2,0), (1,0), (3,0)` cyclically.
      At `i = 0`: `w = p 1 = (2,0)` has unit neighbours `(1,0)` and `(3,0)`, so
      `udeg = 2`; but `p 0 = (0,0)` and `p 2 = (1,0)` lie on the SAME ray from `w`, so
      `∠ (p 0) w (p 2) = 0` and the bound reads `2 ≤ 1`.

  (b) NON-COLLINEAR -- so "assume `S` is not degenerate" does NOT repair it.
      `S = {(0,0), (1,0), (10,1), (0,1)}`, a convex quadrilateral (all four are hull
      vertices).  `w = (0,0)` has unit neighbours `(1,0)` and `(0,1)`, `udeg = 2`.
      List `p = (1,0), (0,0), (10,1), (0,1)`; at `i = 0`,
      `∠ (1,0) (0,0) (10,1) = arctan (1/10) ≈ 0.0997`, so the bound reads
      `2 ≤ 1 + 3(0.0997)/π ≈ 1.095`.

REPAIR: restore H3's binders (`v₀ ∈ interior`, `hne`, the `< π` gap clause and the `= 2π`
central-sum clause), which force `p` to be the argument-sorted listing, OR state the rung
directly against a supplied aperture -- which is `h4_cone_packing`, SEALED above. -/
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

/-! ## THE KERNEL WITNESS -- witness (a), formalised.

`H4Statement` is `h4_cone_bound` verbatim, Prop-ified so it can be negated.  The witness
builds the collinear four-point set and the out-of-order listing described above.  Pattern
(collinear hull ⇒ empty interior ⇒ its own frontier; the three-point zero angle) is reused
from `O06_CollinearRefutation.lean`, which is sealed on this rev. -/

def H4Statement : Prop :=
  ∀ (S : Finset (ℝ^ 2)) (h : ℕ),
    Metric.IsSeparated' 1 (S : Set (ℝ^ 2)) →
    h = (hullPts S).card → 3 ≤ h →
    ∀ p : ℕ → ℝ^ 2,
      (∀ i, p (i + h) = p i) →
      (∀ i < h, p i ∈ hullPts S) →
      (∀ w ∈ hullPts S, ∃ i < h, p i = w) →
      ∀ i : ℕ,
        (udeg S (p (i + 1)) : ℝ)
          ≤ 1 + 3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

theorem pt2_ne {a b c d : ℝ} (h : a ≠ c) : pt2 a b ≠ pt2 c d := by
  intro hEq
  apply h
  have hc := congrArg (fun z => (WithLp.ofLp z) 0) hEq
  simpa [pt2] using hc

theorem pt2_dist (a c : ℝ) : dist (pt2 a 0) (pt2 c 0) = |a - c| := by
  rw [EuclideanSpace.dist_eq]
  have hs : ∑ i : Fin 2, dist ((pt2 a 0).ofLp i) ((pt2 c 0).ofLp i) ^ 2 = (a - c) ^ 2 := by
    first
      | simp [pt2, Fin.sum_univ_two, Real.dist_eq, sq_abs]
      | norm_num [pt2, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  rw [hs]
  exact Real.sqrt_sq_eq_abs _

theorem card_insert' {a : ℝ^ 2} {s : Finset (ℝ^ 2)} (h : a ∉ s) :
    (insert a s).card = s.card + 1 := by
  first
    | exact Finset.card_insert_of_notMem h
    | exact Finset.card_insert_of_not_mem h

noncomputable def W : Finset (ℝ^ 2) := {pt2 0 0, pt2 2 0, pt2 1 0, pt2 3 0}

noncomputable def LL : Submodule ℝ (ℝ^ 2) :=
  LinearMap.ker (EuclideanSpace.proj (1 : Fin 2)).toLinearMap

/-- VERBATIM `hull_interior_empty`, `O06_CollinearRefutation.lean` (SEALED). -/
theorem w_hull_interior_empty (s : Set (ℝ^ 2)) (hs : s ⊆ (LL : Set (ℝ^ 2))) :
    interior (convexHull ℝ s) = ∅ := by
  have hsub : convexHull ℝ s ⊆ (LL : Set (ℝ^ 2)) := convexHull_min hs LL.convex
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hne : (interior (LL : Set (ℝ^ 2))).Nonempty := ⟨x, interior_mono hsub hx⟩
  have htop : LL = ⊤ := Submodule.eq_top_of_nonempty_interior' LL hne
  have hmem : (pt2 0 1) ∈ LL := by rw [htop]; trivial
  simp [LL, EuclideanSpace.proj, pt2] at hmem

theorem W_in_LL : (W : Set (ℝ^ 2)) ⊆ (LL : Set (ℝ^ 2)) := by
  intro x hx
  simp only [W, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [LL, EuclideanSpace.proj, pt2]

theorem W_frontier (v : ℝ^ 2) (hv : v ∈ W) :
    v ∈ frontier (convexHull ℝ (W : Set (ℝ^ 2))) := by
  have hcl : IsClosed (convexHull ℝ (W : Set (ℝ^ 2))) :=
    (W.finite_toSet).isClosed_convexHull (𝕜 := ℝ)
  rw [hcl.frontier_eq, w_hull_interior_empty _ W_in_LL]
  exact ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hv), Set.notMem_empty _⟩

theorem hullPts_W : hullPts W = W := by
  ext v
  simp only [hullPts, Finset.mem_filter]
  exact ⟨fun hv => hv.1, fun hv => ⟨hv, W_frontier v hv⟩⟩

theorem card_W : W.card = 4 := by
  have hne3 : (pt2 1 0 : ℝ^ 2) ∉ ({pt2 3 0} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_singleton]
    intro hEq
    exact absurd hEq (pt2_ne (by norm_num))
  have hne2 : (pt2 2 0 : ℝ^ 2) ∉ ({pt2 1 0, pt2 3 0} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hEq | hEq)
    · exact absurd hEq (pt2_ne (by norm_num))
    · exact absurd hEq (pt2_ne (by norm_num))
  have hne1 : (pt2 0 0 : ℝ^ 2) ∉ ({pt2 2 0, pt2 1 0, pt2 3 0} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hEq | hEq | hEq)
    · exact absurd hEq (pt2_ne (by norm_num))
    · exact absurd hEq (pt2_ne (by norm_num))
    · exact absurd hEq (pt2_ne (by norm_num))
  show ({pt2 0 0, pt2 2 0, pt2 1 0, pt2 3 0} : Finset (ℝ^ 2)).card = 4
  rw [card_insert' hne1, card_insert' hne2, card_insert' hne3, Finset.card_singleton]

theorem W_sep : Metric.IsSeparated' 1 (W : Set (ℝ^ 2)) := by
  intro x hx y hy hxy
  rw [edist_dist, ENNReal.one_le_ofReal]
  simp only [W, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | (rw [pt2_dist, le_abs]; norm_num)

theorem nbrs_W : nbrs W (pt2 2 0) = ({pt2 1 0, pt2 3 0} : Finset (ℝ^ 2)) := by
  have h0 : dist (pt2 2 0) (pt2 0 0) = 2 := by rw [pt2_dist]; norm_num
  have h2 : dist (pt2 2 0) (pt2 2 0) = 0 := by rw [pt2_dist]; norm_num
  have h1 : dist (pt2 2 0) (pt2 1 0) = 1 := by rw [pt2_dist]; norm_num
  have h3 : dist (pt2 2 0) (pt2 3 0) = 1 := by rw [pt2_dist]; norm_num
  ext u
  simp only [nbrs, Finset.mem_filter, W, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, hd⟩
    rcases hu with rfl | rfl | rfl | rfl
    · rw [h0] at hd; norm_num at hd
    · rw [h2] at hd; norm_num at hd
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), h1⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), h3⟩

theorem udeg_W : udeg W (pt2 2 0) = 2 := by
  have hins : (pt2 1 0 : ℝ^ 2) ∉ ({pt2 3 0} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_singleton]
    intro hEq
    exact absurd hEq (pt2_ne (by norm_num))
  rw [udeg, nbrs_W, card_insert' hins, Finset.card_singleton]

/-- The three listed points `p 0, p 1, p 2` of the witness are `(0,0), (2,0), (1,0)`:
`p 0` and `p 2` lie on the SAME ray from `p 1`, so the listed angle is `0`.  (Proof line
VERBATIM from `O06_CollinearRefutation.lean`, same three points.) -/
theorem angle_zero_W :
    EuclideanGeometry.angle (pt2 0 0) (pt2 2 0) (pt2 1 0) = 0 := by
  rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
  norm_num [pt2, EuclideanSpace.norm_eq, Fin.sum_univ_two, inner, vsub_eq_sub]

noncomputable def Wq : ℕ → ℝ^ 2
  | 0 => pt2 0 0
  | 1 => pt2 2 0
  | 2 => pt2 1 0
  | _ => pt2 3 0

noncomputable def wp (i : ℕ) : ℝ^ 2 := Wq (i % 4)

/-- ⛔ THE FROZEN H4 IS FALSE.  Four collinear points, listed `(0,0), (2,0), (1,0), (3,0)`;
at `i = 0` the vertex is `(2,0)`, whose unit neighbours are `(1,0)` and `(3,0)` (so
`udeg = 2`), while `p 0 = (0,0)` and `p 2 = (1,0)` are on one ray from it, so the listed
angle is `0` and the frozen bound reads `2 ≤ 1`. -/
theorem h4_cone_bound_false : ¬ H4Statement := by
  intro H
  have e0 : wp 0 = pt2 0 0 := by first | rfl | norm_num [wp, Wq] | simp [wp, Wq]
  have e1 : wp 1 = pt2 2 0 := by first | rfl | norm_num [wp, Wq] | simp [wp, Wq]
  have e2 : wp 2 = pt2 1 0 := by first | rfl | norm_num [wp, Wq] | simp [wp, Wq]
  have e3 : wp 3 = pt2 3 0 := by first | rfl | norm_num [wp, Wq] | simp [wp, Wq]
  have hper : ∀ i, wp (i + 4) = wp i := by
    intro i
    simp only [wp, Nat.add_mod_right]
  have hmem : ∀ i < 4, wp i ∈ hullPts W := by
    intro i hi
    rw [hullPts_W]
    interval_cases i
    · rw [e0]; simp [W]
    · rw [e1]; simp [W]
    · rw [e2]; simp [W]
    · rw [e3]; simp [W]
  have hsurj : ∀ v ∈ hullPts W, ∃ i < 4, wp i = v := by
    intro v hv
    rw [hullPts_W] at hv
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩
    · exact ⟨2, by norm_num, e2⟩
    · exact ⟨3, by norm_num, e3⟩
  have key := H W 4 W_sep (by rw [hullPts_W, card_W]) (by norm_num) wp hper hmem hsurj 0
  simp only [zero_add] at key
  rw [e0, e1, e2, udeg_W, angle_zero_W] at key
  norm_num at key

/-! ## WITNESS (b) -- NON-COLLINEAR, so "assume `S` is non-degenerate" does NOT repair H4.

`V = {(0,0), (1,0), (10,1), (0,1)}` is a convex quadrilateral: all four points are hull
VERTICES (each is the strict maximiser of an explicit linear functional), so the hull has
nonempty interior and none of `H1`'s degeneracy applies.  Listed `(1,0), (0,0), (10,1),
(0,1)`, the vertex at `i = 0` is `(0,0)`, whose unit neighbours are `(1,0)` and `(0,1)`
(`udeg = 2`), while the LISTED angle `∠ (1,0) (0,0) (10,1) = arctan(1/10) < π/3`, so the
frozen bound reads `2 ≤ 1 + 3·(<π/3)/π < 2`.

The defect is therefore NOT degeneracy of `S`: it is that `hper / hmem / hsurj` leave the
CYCLIC ORDER of `p` free.  `p 0` and `p 2` are not the hull-neighbours of `p 1`. -/

theorem pt2_ne' {a b c d : ℝ} (h : b ≠ d) : pt2 a b ≠ pt2 c d := by
  intro hEq
  apply h
  have hc := congrArg (fun z => (WithLp.ofLp z) 1) hEq
  simpa [pt2] using hc

theorem pt2_dist2 (a b c d : ℝ) :
    dist (pt2 a b) (pt2 c d) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  first
    | simp [pt2, Fin.sum_univ_two, Real.dist_eq, sq_abs]
    | norm_num [pt2, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem le_dist_pt2 (r a b c d : ℝ) (hr : 0 ≤ r) (h : r ^ 2 ≤ (a - c) ^ 2 + (b - d) ^ 2) :
    r ≤ dist (pt2 a b) (pt2 c d) := by
  rw [pt2_dist2]
  have h1 : Real.sqrt (r ^ 2) ≤ Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hr] at h1

theorem pt2_inner (a b c d : ℝ) : (inner ℝ (pt2 a b) (pt2 c d) : ℝ) = a * c + b * d := by
  first
    | (simp [pt2, PiLp.inner_apply, Fin.sum_univ_two]; ring)
    | simp [pt2, PiLp.inner_apply, Fin.sum_univ_two]
    | (norm_num [pt2, Fin.sum_univ_two, inner]; ring)
    | norm_num [pt2, Fin.sum_univ_two, inner]
    | (simp [pt2, Fin.sum_univ_two, inner]; ring)
    | simp [pt2, Fin.sum_univ_two, inner]

noncomputable def fun2 (a b : ℝ) : (ℝ^ 2) →L[ℝ] ℝ := innerSL ℝ (pt2 a b)

theorem fun2_apply (a b c d : ℝ) : fun2 a b (pt2 c d) = a * c + b * d := by
  rw [fun2, innerSL_apply_apply, pt2_inner]

theorem fun2_ne (a b : ℝ) (h : a * a + b * b ≠ 0) : fun2 a b ≠ 0 := by
  intro hz
  have h1 : fun2 a b (pt2 a b) = 0 := by rw [hz]; simp
  rw [fun2_apply] at h1
  exact h h1

/-- A point of `S` maximising a nonzero continuous linear functional over `S` is not in the
interior of the hull: the hull sits in the closed half-space, whose interior misses the
boundary hyperplane.  (Mathlib has the separation theorem but not this converse direction
packaged, which is exactly why `O04` only ever went the other way.) -/
theorem notMem_interior_of_le (S : Finset (ℝ^ 2)) (v : ℝ^ 2)
    (f : (ℝ^ 2) →L[ℝ] ℝ) (hf : f ≠ 0) (hmax : ∀ u ∈ S, f u ≤ f v) :
    v ∉ interior (convexHull ℝ (S : Set (ℝ^ 2))) := by
  intro hv
  have hconv : Convex ℝ {x : ℝ^ 2 | f x ≤ f v} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 : a * f x ≤ a * f v := mul_le_mul_of_nonneg_left hx ha
    have h2 : b * f y ≤ b * f v := mul_le_mul_of_nonneg_left hy hb
    have h3 : a * f v + b * f v = f v := by rw [← add_mul, hab, one_mul]
    linarith
  have hsub : convexHull ℝ (S : Set (ℝ^ 2)) ⊆ {x : ℝ^ 2 | f x ≤ f v} :=
    convexHull_min (fun u hu => hmax u (Finset.mem_coe.mp hu)) hconv
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior v hv
  obtain ⟨z, hz⟩ : ∃ z : ℝ^ 2, 0 < f z := by
    by_contra hcon
    push_neg at hcon
    refine hf (ContinuousLinearMap.ext (fun x => ?_))
    have h1 := hcon x
    have h2 := hcon (-x)
    rw [map_neg] at h2
    simp only [ContinuousLinearMap.zero_apply]
    linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hz
    exact lt_irrefl 0 hz
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnz' : ‖z‖ ≠ 0 := ne_of_gt hnz
  have ht0 : 0 < ε / (2 * ‖z‖) := by positivity
  have hdist : dist (v + (ε / (2 * ‖z‖)) • z) v < ε := by
    have hs : v + (ε / (2 * ‖z‖)) • z - v = (ε / (2 * ‖z‖)) • z := by abel
    rw [dist_eq_norm, hs, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have hkey : ε / (2 * ‖z‖) * ‖z‖ = ε / 2 := by field_simp
    rw [hkey]
    linarith
  have hmem : v + (ε / (2 * ‖z‖)) • z ∈ convexHull ℝ (S : Set (ℝ^ 2)) :=
    interior_subset (hball (Metric.mem_ball.mpr hdist))
  have hle : f (v + (ε / (2 * ‖z‖)) • z) ≤ f v := hsub hmem
  rw [map_add, map_smul, smul_eq_mul] at hle
  nlinarith [ht0, hz]

theorem mem_frontier_of_le (S : Finset (ℝ^ 2)) (v : ℝ^ 2) (hv : v ∈ S)
    (f : (ℝ^ 2) →L[ℝ] ℝ) (hf : f ≠ 0) (hmax : ∀ u ∈ S, f u ≤ f v) :
    v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2))) := by
  have hcl : IsClosed (convexHull ℝ (S : Set (ℝ^ 2))) :=
    (S.finite_toSet).isClosed_convexHull (𝕜 := ℝ)
  rw [hcl.frontier_eq]
  exact ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hv),
    notMem_interior_of_le S v f hf hmax⟩

noncomputable def V : Finset (ℝ^ 2) := {pt2 0 0, pt2 1 0, pt2 10 1, pt2 0 1}

theorem mem_V (u : ℝ^ 2) (hu : u ∈ V) :
    u = pt2 0 0 ∨ u = pt2 1 0 ∨ u = pt2 10 1 ∨ u = pt2 0 1 := by
  simpa [V] using hu

theorem hullPts_V : hullPts V = V := by
  ext v
  simp only [hullPts, Finset.mem_filter]
  refine ⟨fun hv => hv.1, fun hv => ⟨hv, ?_⟩⟩
  rcases mem_V v hv with rfl | rfl | rfl | rfl
  · refine mem_frontier_of_le V _ hv (fun2 (-1) (-1)) (fun2_ne _ _ (by norm_num)) ?_
    intro u hu
    rcases mem_V u hu with rfl | rfl | rfl | rfl <;> (simp only [fun2_apply]; norm_num)
  · refine mem_frontier_of_le V _ hv (fun2 1 (-10)) (fun2_ne _ _ (by norm_num)) ?_
    intro u hu
    rcases mem_V u hu with rfl | rfl | rfl | rfl <;> (simp only [fun2_apply]; norm_num)
  · refine mem_frontier_of_le V _ hv (fun2 1 0) (fun2_ne _ _ (by norm_num)) ?_
    intro u hu
    rcases mem_V u hu with rfl | rfl | rfl | rfl <;> (simp only [fun2_apply]; norm_num)
  · refine mem_frontier_of_le V _ hv (fun2 (-1) 10) (fun2_ne _ _ (by norm_num)) ?_
    intro u hu
    rcases mem_V u hu with rfl | rfl | rfl | rfl <;> (simp only [fun2_apply]; norm_num)

theorem card_V : V.card = 4 := by
  have hne3 : (pt2 10 1 : ℝ^ 2) ∉ ({pt2 0 1} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_singleton]
    intro hEq
    exact absurd hEq (pt2_ne (by norm_num))
  have hne2 : (pt2 1 0 : ℝ^ 2) ∉ ({pt2 10 1, pt2 0 1} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hEq | hEq)
    · exact absurd hEq (pt2_ne (by norm_num))
    · exact absurd hEq (pt2_ne' (by norm_num))
  have hne1 : (pt2 0 0 : ℝ^ 2) ∉ ({pt2 1 0, pt2 10 1, pt2 0 1} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hEq | hEq | hEq)
    · exact absurd hEq (pt2_ne (by norm_num))
    · exact absurd hEq (pt2_ne (by norm_num))
    · exact absurd hEq (pt2_ne' (by norm_num))
  show ({pt2 0 0, pt2 1 0, pt2 10 1, pt2 0 1} : Finset (ℝ^ 2)).card = 4
  rw [card_insert' hne1, card_insert' hne2, card_insert' hne3, Finset.card_singleton]

theorem V_sep : Metric.IsSeparated' 1 (V : Set (ℝ^ 2)) := by
  intro x hx y hy hxy
  rw [edist_dist, ENNReal.one_le_ofReal]
  simp only [V, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | exact le_dist_pt2 1 _ _ _ _ (by norm_num) (by norm_num)

theorem nbrs_V : nbrs V (pt2 0 0) = ({pt2 1 0, pt2 0 1} : Finset (ℝ^ 2)) := by
  have hAA : dist (pt2 0 0) (pt2 0 0) = 0 := dist_self _
  have hAB : dist (pt2 0 0) (pt2 1 0) = 1 := by rw [pt2_dist2]; norm_num
  have hAD : dist (pt2 0 0) (pt2 0 1) = 1 := by rw [pt2_dist2]; norm_num
  have hAC : (2 : ℝ) ≤ dist (pt2 0 0) (pt2 10 1) :=
    le_dist_pt2 2 _ _ _ _ (by norm_num) (by norm_num)
  ext u
  simp only [nbrs, Finset.mem_filter, V, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, hd⟩
    rcases hu with rfl | rfl | rfl | rfl
    · rw [hAA] at hd; norm_num at hd
    · exact Or.inl rfl
    · rw [hd] at hAC; norm_num at hAC
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), hAB⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hAD⟩

theorem udeg_V : udeg V (pt2 0 0) = 2 := by
  have hins : (pt2 1 0 : ℝ^ 2) ∉ ({pt2 0 1} : Finset (ℝ^ 2)) := by
    simp only [Finset.mem_singleton]
    intro hEq
    exact absurd hEq (pt2_ne (by norm_num))
  rw [udeg, nbrs_V, card_insert' hins, Finset.card_singleton]

/-- `∠ (1,0) (0,0) (10,1) = arctan(1/10) < π/3`: law of cosines gives
`√101 · cos θ = 10`, and `√101 < 20` forces `cos θ > 1/2 = cos (π/3)`. -/
theorem angle_lt_pi_div_three_V :
    EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1) < Real.pi / 3 := by
  have hBA : dist (pt2 1 0) (pt2 0 0) = 1 := by rw [pt2_dist2]; norm_num
  have hCA : dist (pt2 10 1) (pt2 0 0) = Real.sqrt 101 := by rw [pt2_dist2]; norm_num
  have hBC : dist (pt2 1 0) (pt2 10 1) = Real.sqrt 82 := by rw [pt2_dist2]; norm_num
  have m82 : Real.sqrt 82 * Real.sqrt 82 = 82 := Real.mul_self_sqrt (by norm_num)
  have m101 : Real.sqrt 101 * Real.sqrt 101 = 101 := Real.mul_self_sqrt (by norm_num)
  have hs101 : 0 < Real.sqrt 101 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 101 < 20 := by
    have h20 : Real.sqrt 400 = 20 := by
      rw [show (400 : ℝ) = 20 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h20]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlaw := EuclideanGeometry.law_cos (pt2 1 0) (pt2 0 0) (pt2 10 1)
  rw [hBA, hCA, hBC, m82, m101] at hlaw
  have hcos : Real.sqrt 101 *
      Real.cos (EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1)) = 10 := by
    first
      | linarith
      | nlinarith [hlaw]
  have hhalf : 1 / 2 < Real.cos (EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1)) := by
    by_contra hc
    push_neg at hc
    have hmul : Real.sqrt 101 *
        Real.cos (EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1))
        ≤ Real.sqrt 101 * (1 / 2) := mul_le_mul_of_nonneg_left hc (le_of_lt hs101)
    rw [hcos] at hmul
    linarith
  by_contra hcon
  push_neg at hcon
  have h0 : 0 ≤ EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hle : EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1) ≤ Real.pi :=
    EuclideanGeometry.angle_le_pi _ _ _
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmono : Real.cos (EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1))
      ≤ Real.cos (Real.pi / 3) := by
    rcases eq_or_lt_of_le hcon with heq | hlt2
    · rw [heq]
    · exact le_of_lt
        (Real.strictAntiOn_cos ⟨by positivity, by linarith⟩ ⟨h0, hle⟩ hlt2)
  rw [Real.cos_pi_div_three] at hmono
  linarith

noncomputable def Vq : ℕ → ℝ^ 2
  | 0 => pt2 1 0
  | 1 => pt2 0 0
  | 2 => pt2 10 1
  | _ => pt2 0 1

noncomputable def vp (i : ℕ) : ℝ^ 2 := Vq (i % 4)

/-- ⛔ THE FROZEN H4 IS FALSE EVEN FOR A STRICTLY CONVEX QUADRILATERAL.  Non-degeneracy is
not the missing hypothesis; the cyclic order is. -/
theorem h4_cone_bound_false_nondegenerate : ¬ H4Statement := by
  intro H
  have e0 : vp 0 = pt2 1 0 := by first | rfl | norm_num [vp, Vq] | simp [vp, Vq]
  have e1 : vp 1 = pt2 0 0 := by first | rfl | norm_num [vp, Vq] | simp [vp, Vq]
  have e2 : vp 2 = pt2 10 1 := by first | rfl | norm_num [vp, Vq] | simp [vp, Vq]
  have e3 : vp 3 = pt2 0 1 := by first | rfl | norm_num [vp, Vq] | simp [vp, Vq]
  have hper : ∀ i, vp (i + 4) = vp i := by
    intro i
    simp only [vp, Nat.add_mod_right]
  have hmem : ∀ i < 4, vp i ∈ hullPts V := by
    intro i hi
    rw [hullPts_V]
    interval_cases i
    · rw [e0]; simp [V]
    · rw [e1]; simp [V]
    · rw [e2]; simp [V]
    · rw [e3]; simp [V]
  have hsurj : ∀ v ∈ hullPts V, ∃ i < 4, vp i = v := by
    intro v hv
    rw [hullPts_V] at hv
    rcases mem_V v hv with rfl | rfl | rfl | rfl
    · exact ⟨1, by norm_num, e1⟩
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨2, by norm_num, e2⟩
    · exact ⟨3, by norm_num, e3⟩
  have key := H V 4 V_sep (by rw [hullPts_V, card_V]) (by norm_num) vp hper hmem hsurj 0
  simp only [zero_add] at key
  rw [e0, e1, e2, udeg_V] at key
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfrac : 3 * EuclideanGeometry.angle (pt2 1 0) (pt2 0 0) (pt2 10 1) / Real.pi < 1 := by
    first
      | rw [div_lt_one hpi]
      | rw [div_lt_one₀ hpi]
    linarith [angle_lt_pi_div_three_V]
  push_cast at key
  linarith

end Erdos1084Upper

#print axioms Erdos1084Upper.h4_packing
#print axioms Erdos1084Upper.h4_halfplane_theta
#print axioms Erdos1084Upper.h4_cone_packing
#print axioms Erdos1084Upper.h4_hull_udeg_le_four
#print axioms Erdos1084Upper.h4_hull_udeg_le_four'
#print axioms Erdos1084Upper.h4_hull_degree_sum_le
#print axioms Erdos1084Upper.h4_cone_bound
#print axioms Erdos1084Upper.notMem_interior_of_le
#print axioms Erdos1084Upper.mem_frontier_of_le
#print axioms Erdos1084Upper.h4_cone_bound_false
#print axioms Erdos1084Upper.h4_cone_bound_false_nondegenerate
