/-
H05_Assembly -- THE PACKAGE PRE-ASSEMBLY (coordinator, 2026-09-05 night, v2)

Proves `o0406_hull_angle_package`'s conclusion from hypotheses that are each either
already sealed or one landing away:
  the degenerate branch     (SEALED: H01_Degenerate.h1_degenerate_udeg_le_two)
  the fan interface         (= H2 SEALED + C's o06_angle_sum_of_polar_fan SEALED
                             + H3 (Contract C, in flight) + C's cone containment,
                             consumed through H04's SEALED h4_cone_packing)
THE DESIGN COLLAPSE, recorded: the existential `alpha` needs only
  Σ_{hull} (udeg − 1) ≤ 3(h−2)
— the slack construction dumps the remainder on one chosen vertex — and BOTH branches
deliver exactly that (degenerate via udeg ≤ 2; fan via one sum_bij reindex + the
per-vertex packing bound).  When H3 lands, the grand splice substitutes sealed theorems
for the interface and the package discharges.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

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

/-! ## The construction lemma: the aggregate bound IS the package -/

theorem package_of_sum_bound (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (hsum : (∑ v ∈ hullPts S, (udeg S v : ℝ)) ≤ 4 * h - 6) :
    ∃ alpha : ℝ^ 2 → ℝ,
      (∀ v ∈ hullPts S, (udeg S v : ℝ) ≤ 1 + 3 * alpha v / Real.pi) ∧
      (∑ v ∈ hullPts S, alpha v = ((h : ℝ) - 2) * Real.pi) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have hne : (hullPts S).Nonempty := by
    rw [← Finset.card_pos, ← hh]
    omega
  obtain ⟨w₀, hw₀⟩ := hne
  set base : ℝ^ 2 → ℝ := fun w => ((udeg S w : ℝ) - 1) * Real.pi / 3 with hbase
  have hsb : (∑ v ∈ hullPts S, base v)
      = ((∑ v ∈ hullPts S, (udeg S v : ℝ)) - h) * Real.pi / 3 := by
    rw [hbase]
    rw [← Finset.sum_div, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, ← hh]
    simp [nsmul_eq_mul]
  set slack : ℝ := ((h : ℝ) - 2) * Real.pi - ∑ v ∈ hullPts S, base v with hslack
  have hslack0 : 0 ≤ slack := by
    rw [hslack, hsb]
    have h1 : (∑ v ∈ hullPts S, (udeg S v : ℝ)) - h ≤ 3 * ((h : ℝ) - 2) := by
      linarith [hsum]
    have h2 := mul_le_mul_of_nonneg_right h1 hpi.le
    linarith [h2]
  refine ⟨fun w => base w + (if w = w₀ then slack else 0), ?_, ?_⟩
  · intro v hv
    have hite : (0 : ℝ) ≤ (if v = w₀ then slack else 0) := by
      split
      · exact hslack0
      · exact le_refl 0
    have hb0 : ((udeg S v : ℝ) - 1) * Real.pi / 3
        ≤ base v + (if v = w₀ then slack else 0) := by
      rw [hbase]
      linarith [hite]
    have hcanc : 3 * (((udeg S v : ℝ) - 1) * Real.pi / 3) / Real.pi
        = (udeg S v : ℝ) - 1 := by
      field_simp
    have hmono := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 3)) hpi.le
    calc (udeg S v : ℝ)
        = 1 + (3 * (((udeg S v : ℝ) - 1) * Real.pi / 3) / Real.pi) := by
          rw [hcanc]; ring
      _ ≤ 1 + 3 * (base v + (if v = w₀ then slack else 0)) / Real.pi := by
          linarith [hmono]
  · rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' (hullPts S) w₀ (fun _ => slack)]
    simp only [hw₀, if_true]
    rw [hslack]
    ring

/-! ## Branch 1: the degenerate case delivers the aggregate bound -/

theorem sum_bound_degenerate (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (hH1 : ∀ v ∈ S, udeg S v ≤ 2) :
    (∑ v ∈ hullPts S, (udeg S v : ℝ)) ≤ 4 * h - 6 := by
  have hsub : ∀ v ∈ hullPts S, (udeg S v : ℝ) ≤ 2 := by
    intro v hv
    have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
    exact_mod_cast hH1 v hvS
  have hcast : (3 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h3
  calc (∑ v ∈ hullPts S, (udeg S v : ℝ))
      ≤ ∑ _v ∈ hullPts S, (2 : ℝ) := Finset.sum_le_sum hsub
    _ = 2 * h := by
        rw [Finset.sum_const, ← hh]
        simp [nsmul_eq_mul, mul_comm]
    _ ≤ 4 * h - 6 := by linarith

/-! ## Branch 2: the fan interface delivers the aggregate bound -/

/-- The fan interface: an h-periodic listing of the hull points (positions `1..h`),
injective and surjective there, whose listed angles sum to `(h−2)π`, with the per-vertex
packing bound at the listed aperture — the shape that H2 + Contract C's fan theorem + H3
+ the cone containment (through H04's sealed `h4_cone_packing`) jointly produce. -/
def FanInterface (S : Finset (ℝ^ 2)) (h : ℕ) : Prop :=
  ∃ p : ℕ → ℝ^ 2,
    (∀ i < h, p (i + 1) ∈ hullPts S) ∧
    (∀ w ∈ hullPts S, ∃ i < h, p (i + 1) = w) ∧
    (∀ i < h, ∀ j < h, p (i + 1) = p (j + 1) → i = j) ∧
    (∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi) ∧
    (∀ i < h, (udeg S (p (i + 1)) : ℝ)
      ≤ 1 + 3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi)

theorem sum_bound_of_fan (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (hfan : FanInterface S h) :
    (∑ v ∈ hullPts S, (udeg S v : ℝ)) ≤ 4 * h - 6 := by
  classical
  obtain ⟨p, hmem, hsurj, hinj, hsum, hbound⟩ := hfan
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have hre : (∑ i ∈ Finset.range h, (udeg S (p (i + 1)) : ℝ))
      = ∑ v ∈ hullPts S, (udeg S v : ℝ) := by
    refine Finset.sum_bij (fun i _ => p (i + 1)) ?_ ?_ ?_ ?_
    · intro a ha
      exact hmem a (Finset.mem_range.mp ha)
    · intro a ha b hb hab
      exact hinj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) hab
    · intro w hw
      obtain ⟨i, hi, hpi'⟩ := hsurj w hw
      exact ⟨i, Finset.mem_range.mpr hi, hpi'⟩
    · intro a _
      rfl
  rw [← hre]
  have hstep : (∑ i ∈ Finset.range h, (udeg S (p (i + 1)) : ℝ))
      ≤ ∑ i ∈ Finset.range h,
          (1 + 3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact hbound i (Finset.mem_range.mp hi)
  have hterm : ∀ i ∈ Finset.range h,
      3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi
        = (3 / Real.pi) * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) := by
    intro i _
    ring
  have hval : (∑ i ∈ Finset.range h,
      (1 + 3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi))
      = 4 * h - 6 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum]
    field_simp
    ring
  calc (∑ i ∈ Finset.range h, (udeg S (p (i + 1)) : ℝ))
      ≤ (∑ i ∈ Finset.range h,
          (1 + 3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi)) := hstep
    _ = 4 * h - 6 := hval

/-! ## The master pre-assembly -/

theorem hull_angle_package_pre (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (hbranch : (∀ v ∈ S, udeg S v ≤ 2) ∨ FanInterface S h) :
    ∃ alpha : ℝ^ 2 → ℝ,
      (∀ v ∈ hullPts S, (udeg S v : ℝ) ≤ 1 + 3 * alpha v / Real.pi) ∧
      (∑ v ∈ hullPts S, alpha v = ((h : ℝ) - 2) * Real.pi) :=
  package_of_sum_bound S h hh h3
    (hbranch.elim (sum_bound_degenerate S h hh h3) (sum_bound_of_fan S h hh h3))

end Erdos1084Upper

#print axioms Erdos1084Upper.hull_angle_package_pre
