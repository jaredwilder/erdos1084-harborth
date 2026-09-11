import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O03, UNIT-DEGREE AT MOST 6

A point `v` has at most six unit-distance neighbours inside a 1-separated set `S`.

⭐ THIS FILE CARRIES NO `sorry`, AND IT DOES NOT USE O02.  The campaign report routed O03
through the cyclic order (O2).  It does not need it: six half-open argument buckets of
width `π/3` cover `(-π, π]`, so seven neighbours put two in one bucket, their argument
gap is `< π/3`, and `angle ≤ |Δarg|` (O02c) contradicts `π/3 ≤ angle` (O01).
PIGEONHOLE, not cyclic order.

The two upstream rungs are carried as EXPLICIT BINDERS -- `h60` is verbatim O01's
conclusion and `hgap` is verbatim the O02a+O02d+O02c chain's conclusion -- so this file
assumes nothing it does not name, and `depends_on` in the DAG says which rung supplies
which binder.

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.
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
