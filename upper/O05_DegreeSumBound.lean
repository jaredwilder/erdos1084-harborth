import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O05, THE AGGREGATE DEGREE-SUM BOUND

`∑_{v ∈ S} deg v + 2h + 6 ≤ 6n`, i.e. the subtraction-free form of
`∑ deg ≤ 6n - 2h - 6`.  STATEMENT FROZEN -- verbatim from
`O05_DegreeSumBound_SCAFFOLD.lean`, not reworded.

WHAT THIS FILE ESTABLISHES OUTRIGHT -- each of these carries the CLEAN axiom triple
`[propext, Classical.choice, Quot.sound]`, verified by the `#print axioms` block at the
bottom of the file:
  * `o01_sixty` -- the 60-degree lemma (rung O01), law of cosines + antitonicity of `cos`
    on `[0, π]`.  REAL PROOF.
  * `abs_toReal_coe_le` -- reducing a real mod `2π` never increases `|·|`.  REAL PROOF.
  * `o02_argument_function` -- rung O02 (= O02a + O02c + O02d): an argument function `θ` on
    `ℝ^2` valued in `(-π, π]` with `angle u v w ≤ |θ u - θ w|`, built from
    `Orientation.oangle` (`θ x := (o.oangle e (x - v)).toReal`).  This rung was carried in
    the SEALED O03 as three explicit binders; it is now DISCHARGED here.  REAL PROOF.
  * `o03_interior_degree_le_six` -- verbatim the SEALED O03 (pigeonhole on six argument
    buckets of width `π/3`).  REAL PROOF.
  * `o03_udeg_le_six` -- `udeg S v ≤ 6` with BOTH O03 binders discharged (O01 supplies
    `h60`, O02 supplies `θ`).  REAL PROOF, no hypotheses beyond 1-separation.

WHAT REMAINS -- exactly ONE `sorry`, named and type-checked:
  * `o0406_hull_angle_package` -- rungs O04 (supporting line ⇒ `deg v ≤ 1 + 3αᵥ/π` at a hull
    vertex) and O06 (`∑_{hull} αᵥ = (h-2)π`) delivered together, because the per-vertex bound
    is only usable against the AGGREGATE angle sum.  Deliberately NOT split into two lemmas:
    without a Mathlib definition of "the interior angle of the hull polygon at `v`" a split
    is unsound as a factoring -- O06 alone would be satisfiable by a fake `α` that then makes
    O04 unprovable.  This is the genuinely new geometry and it has NO Mathlib substrate:
    convex-polygon interior angles at the vertices of `frontier (convexHull ℝ S)` do not
    exist in Mathlib in any usable form, so this rung is a development, not a lemma.

STATUS: PARTIAL -- O01, O02, O03 and the whole O05 assembly (hull/interior split, ℕ↔ℝ cast
discipline, final arithmetic `6(n-h) + (h + 3(h-2)) = 6n - 2h - 6`) are REAL; the single
remaining gap is the hull-angle package O04+O06.
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

/-! ### O01 -- the sixty-degree lemma (REAL PROOF, no `sorry` beneath) -/

/-- Two unit-distance neighbours of `p` that are themselves at distance `≥ 1` subtend an
angle of at least `π/3` at `p`.  Law of cosines plus antitonicity of `cos` on `[0, π]`. -/
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

/-! ### O02 -- the argument function (REAL PROOF, no `sorry` beneath) -/

/-- The wrap step: reducing a real mod `2π` never increases its absolute value.  This is
the whole content of "the angle is at most the argument gap": if the gap already lies in
`(-π, π]` the reduction is the identity, and otherwise the reduced value is bounded by `π`
while the gap is not. -/
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

/-- Rung O02 (= O02a + O02c + O02d).  There is an argument function on `ℝ^2`, valued in
`(-π, π]`, whose coordinate difference dominates the unoriented angle at `v`.

`θ x := (o.oangle e (x - v)).toReal` for a fixed orientation `o` of `ℝ^2` and a nonzero
reference `e`.  The range is free (`Real.Angle.toReal` always lands in `(-π, π]`).  The gap
is `Orientation.oangle_add` (oriented angles at `v` are additive, so the oriented angle from
`u` to `w` is `θ w - θ u` *in `Real.Angle`*) followed by
`Orientation.angle_eq_abs_oangle_toReal` and the wrap lemma above. -/
theorem o02_argument_function (S : Finset (ℝ^ 2)) (v : ℝ^ 2) :
    ∃ theta : ℝ^ 2 → ℝ,
      (∀ u ∈ S, -Real.pi < theta u) ∧
      (∀ u ∈ S, theta u ≤ Real.pi) ∧
      (∀ u ∈ S, ∀ w ∈ S, dist v u = 1 → dist v w = 1 →
        EuclideanGeometry.angle u v w ≤ |theta u - theta w|) := by
  haveI : Fact (Module.finrank ℝ (ℝ^ 2) = 2) := ⟨finrank_euclideanSpace_fin⟩
  have hB := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  refine ⟨fun x => (hB.orientation.oangle (hB 0) (x - v)).toReal, ?_, ?_, ?_⟩
  · intro u _
    exact Real.Angle.neg_pi_lt_toReal _
  · intro u _
    exact Real.Angle.toReal_le_pi _
  · intro u _ w _ hdu hdw
    try dsimp only
    have hune : u - v ≠ 0 := by
      intro hz
      rw [sub_eq_zero] at hz
      rw [hz, dist_self] at hdu
      norm_num at hdu
    have hwne : w - v ≠ 0 := by
      intro hz
      rw [sub_eq_zero] at hz
      rw [hz, dist_self] at hdw
      norm_num at hdw
    have hene : (hB 0 : ℝ^ 2) ≠ 0 := hB.ne_zero 0
    have hdef : EuclideanGeometry.angle u v w
        = InnerProductGeometry.angle (u - v) (w - v) := rfl
    have hangle : EuclideanGeometry.angle u v w
        = |(hB.orientation.oangle (u - v) (w - v)).toReal| := by
      rw [hdef, Orientation.angle_eq_abs_oangle_toReal hB.orientation hune hwne]
    have hadd := Orientation.oangle_add hB.orientation hene hune hwne
    have hsub : hB.orientation.oangle (u - v) (w - v)
        = hB.orientation.oangle (hB 0) (w - v)
          - hB.orientation.oangle (hB 0) (u - v) := by
      rw [← hadd]; abel
    have hAB : hB.orientation.oangle (hB 0) (w - v)
          - hB.orientation.oangle (hB 0) (u - v)
        = ((((hB.orientation.oangle (hB 0) (w - v)).toReal
            - (hB.orientation.oangle (hB 0) (u - v)).toReal : ℝ)) : Real.Angle) := by
      rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    rw [hangle, hsub, hAB]
    refine le_trans (abs_toReal_coe_le _) ?_
    first
      | rw [abs_sub_comm]
      | exact le_of_eq (abs_sub_comm _ _)

/-! ### O03 -- unit degree at most six (VERBATIM the SEALED `O03_InteriorDegreeLeSix.lean`) -/

theorem o03_interior_degree_le_six (S : Finset (ℝ^ 2)) (v : ℝ^ 2)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (theta : ℝ^ 2 → ℝ)
    (hlo : ∀ u ∈ S, -Real.pi < theta u)
    (hhi : ∀ u ∈ S, theta u ≤ Real.pi)
    (hgap : ∀ u ∈ S, ∀ w ∈ S, dist v u = 1 → dist v w = 1 →
      EuclideanGeometry.angle u v w ≤ |theta u - theta w|)
    (h60 : ∀ p q r : ℝ^ 2, dist p q = 1 → dist p r = 1 → 1 ≤ dist q r →
      Real.pi / 3 ≤ EuclideanGeometry.angle q p r) :
    (S.filter (fun u => dist v u = 1)).card ≤ 6 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsepP : (S : Set (ℝ^ 2)).Pairwise (fun p q => (1 : ℝ≥0∞) ≤ edist p q) := hsep
  have hrange : ∀ u ∈ S, (0 : ℤ) ≤ ⌊3 * (Real.pi - theta u) / Real.pi⌋ ∧
      ⌊3 * (Real.pi - theta u) / Real.pi⌋ < 6 := by
    intro u hu
    have h1 : -Real.pi < theta u := hlo u hu
    have h2 : theta u ≤ Real.pi := hhi u hu
    constructor
    · exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hpi.le)
    · refine Int.floor_lt.mpr ?_
      push_cast
      first
        | rw [div_lt_iff hpi]
        | rw [div_lt_iff₀ hpi]
      linarith
  by_contra hcon
  push_neg at hcon
  have hcard : (Finset.range 6).card < (S.filter (fun u => dist v u = 1)).card := by
    rw [Finset.card_range]
    omega
  have hmaps : ∀ u ∈ S.filter (fun u => dist v u = 1),
      (⌊3 * (Real.pi - theta u) / Real.pi⌋).toNat ∈ Finset.range 6 := by
    intro u hu
    have huS : u ∈ S := (Finset.mem_filter.mp hu).1
    obtain ⟨ha, hb⟩ := hrange u huS
    rw [Finset.mem_range]
    omega
  obtain ⟨x, hx, y, hy, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
  have hxd : dist v x = 1 := (Finset.mem_filter.mp hx).2
  have hyd : dist v y = 1 := (Finset.mem_filter.mp hy).2
  have hdxy : (1 : ℝ) ≤ dist x y := by
    have he : (1 : ℝ≥0∞) ≤ edist x y :=
      hsepP (Finset.mem_coe.mpr hxS) (Finset.mem_coe.mpr hyS) hxy
    rw [edist_dist] at he
    exact ENNReal.one_le_ofReal.mp he
  have hang : Real.pi / 3 ≤ EuclideanGeometry.angle x v y := h60 v x y hxd hyd hdxy
  have hle : EuclideanGeometry.angle x v y ≤ |theta x - theta y| := hgap x hxS y hyS hxd hyd
  obtain ⟨hax, hbx⟩ := hrange x hxS
  obtain ⟨hay, hby⟩ := hrange y hyS
  have hfloor : ⌊3 * (Real.pi - theta x) / Real.pi⌋ = ⌊3 * (Real.pi - theta y) / Real.pi⌋ := by
    omega
  have habs : |3 * (Real.pi - theta x) / Real.pi - 3 * (Real.pi - theta y) / Real.pi| < 1 := by
    have hA1 := Int.floor_le (3 * (Real.pi - theta x) / Real.pi)
    have hA2 := Int.lt_floor_add_one (3 * (Real.pi - theta x) / Real.pi)
    have hB1 := Int.floor_le (3 * (Real.pi - theta y) / Real.pi)
    have hB2 := Int.lt_floor_add_one (3 * (Real.pi - theta y) / Real.pi)
    rw [hfloor] at hA1 hA2
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have heq : 3 * (Real.pi - theta x) / Real.pi - 3 * (Real.pi - theta y) / Real.pi
      = (3 * (theta y - theta x)) / Real.pi := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hpi] at habs
  first
    | rw [div_lt_one hpi] at habs
    | rw [div_lt_one₀ hpi] at habs
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < 3 by norm_num), abs_sub_comm] at habs
  linarith

/-- O03 against the `udeg` definition, with O01 discharging the `h60` binder and O02
supplying the argument function. -/
theorem o03_udeg_le_six (S : Finset (ℝ^ 2)) (v : ℝ^ 2)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2))) :
    Erdos1084Upper.udeg S v ≤ 6 := by
  obtain ⟨theta, hlo, hhi, hgap⟩ := o02_argument_function S v
  have hkey := o03_interior_degree_le_six S v hsep theta hlo hhi hgap o01_sixty
  have hrw : Erdos1084Upper.udeg S v = (S.filter (fun u => dist v u = 1)).card := by
    first
      | rfl
      | simp [Erdos1084Upper.udeg, Erdos1084Upper.nbrs]
  rw [hrw]
  exact hkey

/-! ### O04 + O06 -- GAP.  The hull-angle package. -/

/-- ⛔ GAP (rungs O04 + O06).  At each hull vertex `v` the neighbours lie inside a cone of
aperture `αᵥ` cut out by a supporting line, so the O01 sixty-degree spacing gives
`deg v ≤ 1 + 3αᵥ/π`; and the interior angles of the hull polygon sum to `(h-2)π`.
Delivered as ONE package because the per-vertex bound is only usable against the aggregate
angle sum (with a merely closed supporting half-plane the aperture can be exactly `π`,
admitting FOUR neighbours at `3 × 60°`, and the per-vertex peel then loses by 3). -/
theorem o0406_hull_angle_package (S : Finset (ℝ^ 2)) (h : ℕ)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hh : h = (Erdos1084Upper.hullPts S).card) (h3 : 3 ≤ h) :
    ∃ alpha : ℝ^ 2 → ℝ,
      (∀ v ∈ Erdos1084Upper.hullPts S,
        (Erdos1084Upper.udeg S v : ℝ) ≤ 1 + 3 * alpha v / Real.pi) ∧
      (∑ v ∈ Erdos1084Upper.hullPts S, alpha v = ((h : ℝ) - 2) * Real.pi) := by
  sorry

/-! ### O05 -- the assembly (REAL PROOF given the two gaps above) -/

theorem o05_degree_sum_bound (S : Finset (ℝ^ 2)) (n h : ℕ)
    (hsep : Metric.IsSeparated' 1 (S : Set (ℝ^ 2)))
    (hn : n = S.card) (hh : h = (Erdos1084Upper.hullPts S).card) (h3 : 3 ≤ h) :
    (∑ v ∈ S, Erdos1084Upper.udeg S v) + 2 * h + 6 ≤ 6 * n := by
  have hpine : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hHsub : Erdos1084Upper.hullPts S ⊆ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hHle : (Erdos1084Upper.hullPts S).card ≤ S.card := Finset.card_le_card hHsub
  -- NOTE (rev drift): on this Mathlib rev `Finset.card_sdiff` is UNCONDITIONAL and reads
  -- `#(A \ B) = #A - #(B ∩ A)`, so it takes no subset argument.
  have hcardsd : (S \ Erdos1084Upper.hullPts S).card
      + (Erdos1084Upper.hullPts S).card = S.card := by
    first
      | exact Finset.card_sdiff_add_card_eq_card hHsub
      | (rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hHsub]; omega)
  have hcard : (S \ Erdos1084Upper.hullPts S).card + h = n := by omega
  have hsplit : (∑ v ∈ S \ Erdos1084Upper.hullPts S, Erdos1084Upper.udeg S v)
      + (∑ v ∈ Erdos1084Upper.hullPts S, Erdos1084Upper.udeg S v)
      = ∑ v ∈ S, Erdos1084Upper.udeg S v := Finset.sum_sdiff hHsub
  have hint : (∑ v ∈ S \ Erdos1084Upper.hullPts S, Erdos1084Upper.udeg S v)
      ≤ 6 * (S \ Erdos1084Upper.hullPts S).card := by
    calc (∑ v ∈ S \ Erdos1084Upper.hullPts S, Erdos1084Upper.udeg S v)
        ≤ ∑ _v ∈ S \ Erdos1084Upper.hullPts S, 6 :=
          Finset.sum_le_sum (fun v _ => o03_udeg_le_six S v hsep)
      _ = 6 * (S \ Erdos1084Upper.hullPts S).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨alpha, hdeg, hsum⟩ := o0406_hull_angle_package S h hsep hh h3
  have hhullR : ((∑ v ∈ Erdos1084Upper.hullPts S, Erdos1084Upper.udeg S v : ℕ) : ℝ)
      ≤ 4 * (h : ℝ) - 6 := by
    have hle := Finset.sum_le_sum hdeg
    have hd : ∑ v ∈ Erdos1084Upper.hullPts S, 3 * alpha v / Real.pi
        = (3 * ∑ v ∈ Erdos1084Upper.hullPts S, alpha v) / Real.pi := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    have hrw : ∑ v ∈ Erdos1084Upper.hullPts S, (1 + 3 * alpha v / Real.pi)
        = (h : ℝ) + 3 * ((h : ℝ) - 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← hh, hd, hsum]
      first
        | (field_simp; ring)
        | field_simp
    rw [hrw] at hle
    push_cast at hle ⊢
    linarith
  have hhullN : (∑ v ∈ Erdos1084Upper.hullPts S, Erdos1084Upper.udeg S v) + 6 ≤ 4 * h := by
    have hc : (((∑ v ∈ Erdos1084Upper.hullPts S, Erdos1084Upper.udeg S v) + 6 : ℕ) : ℝ)
        ≤ ((4 * h : ℕ) : ℝ) := by push_cast at hhullR ⊢; linarith
    exact_mod_cast hc
  omega

/-! ### Axiom receipts.  The first five MUST show exactly
`[propext, Classical.choice, Quot.sound]`; only `o05_degree_sum_bound` may carry `sorryAx`,
and it carries it for exactly one reason -- `o0406_hull_angle_package`. -/

#print axioms o01_sixty
#print axioms abs_toReal_coe_le
#print axioms o02_argument_function
#print axioms o03_interior_degree_le_six
#print axioms o03_udeg_le_six
#print axioms o05_degree_sum_bound
