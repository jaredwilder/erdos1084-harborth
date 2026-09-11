import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

theorem o02a_polar_coordinates (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    ∃ t : ℝ, -Real.pi < t ∧ t ≤ Real.pi ∧ Real.cos t = x ∧ Real.sin t = y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx1 hx2
  have hsin : Real.sin (Real.arccos x) = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  have habs : Real.sqrt (1 - x ^ 2) = |y| := by
    rw [show (1 : ℝ) - x ^ 2 = y ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  have h0 : 0 ≤ Real.arccos x := Real.arccos_nonneg x
  have hup : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
  rcases le_or_gt 0 y with hy | hy
  · refine ⟨Real.arccos x, by linarith, hup, hcos, ?_⟩
    rw [hsin, habs, abs_of_nonneg hy]
  · have hne : Real.arccos x ≠ Real.pi := by
      intro hEq
      have hz : Real.sin (Real.arccos x) = 0 := by rw [hEq, Real.sin_pi]
      rw [hsin, habs] at hz
      have hy0 : y = 0 := abs_eq_zero.mp hz
      linarith
    have hlt : Real.arccos x < Real.pi := lt_of_le_of_ne hup hne
    refine ⟨-Real.arccos x, by linarith, by linarith, ?_, ?_⟩
    · rw [Real.cos_neg]
      exact hcos
    · rw [Real.sin_neg, hsin, habs, abs_of_neg hy]
      ring

theorem o02b_arccos_cos_le_abs (t : ℝ) : Real.arccos (Real.cos t) ≤ |t| := by
  have hcos : Real.cos t = Real.cos |t| := by
    rcases abs_cases t with ⟨hb, _⟩ | ⟨hb, _⟩
    · rw [hb]
    · rw [hb, Real.cos_neg]
  rcases le_or_gt |t| Real.pi with h | h
  · rw [hcos, Real.arccos_cos (abs_nonneg t) h]
  · exact le_trans (Real.arccos_le_pi (Real.cos t)) h.le

theorem o02c_angle_le_arg_gap (v u w : ℝ^ 2) (a b : ℝ)
    (hu : dist v u = 1) (hw : dist v w = 1)
    (hd : dist u w ^ 2 = 2 - 2 * Real.cos (a - b))
    (harccos : ∀ t : ℝ, Real.arccos (Real.cos t) ≤ |t|) :
    EuclideanGeometry.angle u v w ≤ |a - b| := by
  have h0 : 0 ≤ EuclideanGeometry.angle u v w := EuclideanGeometry.angle_nonneg u v w
  have hle : EuclideanGeometry.angle u v w ≤ Real.pi := EuclideanGeometry.angle_le_pi u v w
  have hlaw := EuclideanGeometry.law_cos u v w
  rw [dist_comm u v, dist_comm w v, hu, hw] at hlaw
  have hsq : dist u w ^ 2 = dist u w * dist u w := by ring
  rw [hsq] at hd
  have hcosang : Real.cos (EuclideanGeometry.angle u v w) = Real.cos (a - b) := by
    linarith [hlaw, hd]
  have hid : EuclideanGeometry.angle u v w
      = Real.arccos (Real.cos (EuclideanGeometry.angle u v w)) :=
    (Real.arccos_cos h0 hle).symm
  rw [hid, hcosang]
  exact harccos (a - b)

theorem o02d_unit_chord_identity (v u w : ℝ^ 2) (a b : ℝ)
    (hu0 : u.ofLp 0 = v.ofLp 0 + Real.cos a) (hu1 : u.ofLp 1 = v.ofLp 1 + Real.sin a)
    (hw0 : w.ofLp 0 = v.ofLp 0 + Real.cos b) (hw1 : w.ofLp 1 = v.ofLp 1 + Real.sin b) :
    dist u w ^ 2 = 2 - 2 * Real.cos (a - b) := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, hu0, hu1, hw0, hw1, Real.cos_sub]
  linear_combination Real.sin_sq_add_cos_sq a + Real.sin_sq_add_cos_sq b

theorem o02e_cyclic_gap_sum (m : ℕ) (a : ℕ → ℝ) (hwrap : a m = a 0 + 2 * Real.pi) :
    ∑ i ∈ Finset.range m, (a (i + 1) - a i) = 2 * Real.pi := by
  rw [Finset.sum_range_sub a m, hwrap]
  ring

theorem o01_sixty_degree_gap (x y z : ℝ^ 2)
    (hxy : dist x y = 1) (hxz : dist x z = 1) (hyz : 1 ≤ dist y z) :
    Real.pi / 3 ≤ EuclideanGeometry.angle y x z := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdyz : (0 : ℝ) ≤ dist y z := dist_nonneg
  have h0 : 0 ≤ EuclideanGeometry.angle y x z := EuclideanGeometry.angle_nonneg y x z
  have hle : EuclideanGeometry.angle y x z ≤ Real.pi := EuclideanGeometry.angle_le_pi y x z
  by_contra hcon
  push_neg at hcon
  have hmem1 : EuclideanGeometry.angle y x z ∈ Set.Icc 0 Real.pi := Set.mem_Icc.mpr ⟨h0, hle⟩
  have hmem2 : Real.pi / 3 ∈ Set.Icc 0 Real.pi := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hcos : Real.cos (Real.pi / 3) < Real.cos (EuclideanGeometry.angle y x z) :=
    Real.strictAntiOn_cos hmem1 hmem2 hcon
  rw [Real.cos_pi_div_three] at hcos
  have hlaw := EuclideanGeometry.law_cos y x z
  rw [dist_comm y x, dist_comm z x, hxy, hxz] at hlaw
  nlinarith [hlaw, hcos, hyz, hdyz]

/-! ## O02, REPAIRED. The frozen statement plus the hypothesis `D.Nonempty`.
The frozen form is FALSE (O02_EmptyRefutation.lean): `D = ∅` satisfies both hypotheses and
makes the wrap clause read `a 0 = a 0 + 2π`.  Everything below is the frozen conclusion
verbatim under that one added hypothesis. -/

theorem unit_dist_sq (v u : ℝ^ 2) (h : dist v u = 1) :
    (u.ofLp 0 - v.ofLp 0) ^ 2 + (u.ofLp 1 - v.ofLp 1) ^ 2 = 1 := by
  have hd := EuclideanSpace.dist_eq v u
  rw [h] at hd
  have h2 : ((1:ℝ))^2 = (Real.sqrt (∑ i, dist (v.ofLp i) (u.ofLp i) ^ 2))^2 := by rw [← hd]
  rw [Real.sq_sqrt (by positivity)] at h2
  simp [Fin.sum_univ_two, Real.dist_eq] at h2
  nlinarith [sq_abs (v.ofLp 0 - u.ofLp 0), sq_abs (v.ofLp 1 - u.ofLp 1)]

theorem pt_ext (u w : ℝ^ 2) (h0 : u.ofLp 0 = w.ofLp 0) (h1 : u.ofLp 1 = w.ofLp 1) : u = w := by
  ext i; fin_cases i <;> simpa using ‹_›

theorem o02_cyclic_angular_order_repaired (v : ℝ^ 2) (D : Finset (ℝ^ 2))
    (hne : D.Nonempty)
    (hunit : ∀ u ∈ D, dist v u = 1)
    (hsep : ∀ u ∈ D, ∀ w ∈ D, u ≠ w → 1 ≤ dist u w) :
    ∃ a : ℕ → ℝ,
      (∀ i, i < D.card → -Real.pi < a i ∧ a i ≤ Real.pi) ∧
      (∀ i, i + 1 < D.card → a i < a (i + 1)) ∧
      a D.card = a 0 + 2 * Real.pi ∧
      (∀ i, i < D.card → Real.pi / 3 ≤ a (i + 1) - a i) ∧
      ∑ i ∈ Finset.range D.card, (a (i + 1) - a i) = 2 * Real.pi := by
  classical
  -- 1. a polar argument for every neighbour, total by a junk value off `D`
  have coordT : ∀ u : ℝ^ 2, ∃ t : ℝ, u ∈ D →
      (-Real.pi < t ∧ t ≤ Real.pi ∧
        u.ofLp 0 = v.ofLp 0 + Real.cos t ∧ u.ofLp 1 = v.ofLp 1 + Real.sin t) := by
    intro u
    by_cases hu : u ∈ D
    · obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
        o02a_polar_coordinates (u.ofLp 0 - v.ofLp 0) (u.ofLp 1 - v.ofLp 1)
          (unit_dist_sq v u (hunit u hu))
      exact ⟨t, fun _ => ⟨ht1, ht2, by linarith, by linarith⟩⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose θ hθ using coordT
  -- 2. the argument map is injective on `D`
  have hinj : Set.InjOn θ D := by
    intro u hu w hw h
    obtain ⟨-, -, hu0, hu1⟩ := hθ u hu
    obtain ⟨-, -, hw0, hw1⟩ := hθ w hw
    exact pt_ext u w (by rw [hu0, hw0, h]) (by rw [hu1, hw1, h])
  set A : Finset ℝ := D.image θ with hA
  have hcard : A.card = D.card := Finset.card_image_of_injOn hinj
  set m : ℕ := D.card with hm
  have hmpos : 0 < m := Finset.card_pos.mpr hne
  have hApos : 0 < A.card := by rw [hcard]; exact hmpos
  set e := A.orderIsoOfFin (rfl : A.card = A.card) with he
  set a : ℕ → ℝ := fun i => if h : i < A.card then (e ⟨i, h⟩ : ℝ)
      else ((e ⟨0, hApos⟩ : ℝ) + 2 * Real.pi) with ha
  -- 3. reading `a` below the wrap
  have hbelow : ∀ i (h : i < m), a i = (e ⟨i, by rw [hcard]; exact h⟩ : ℝ) := by
    intro i h
    have h' : i < A.card := by rw [hcard]; exact h
    simp only [ha, dif_pos h']
  have hmem : ∀ i (h : i < m), a i ∈ A := by
    intro i h; rw [hbelow i h]; exact (e _).2
  have hwrap : a m = a 0 + 2 * Real.pi := by
    have hnot : ¬ (m < A.card) := by rw [hcard]; exact lt_irrefl m
    have h0 : (0:ℕ) < A.card := hApos
    simp only [ha, dif_neg hnot, dif_pos h0]
  -- 4. bounds
  have hbounds : ∀ i, i < m → -Real.pi < a i ∧ a i ≤ Real.pi := by
    intro i h
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp (hmem i h)
    obtain ⟨h1, h2, -, -⟩ := hθ u hu
    exact ⟨by rw [← hux]; exact h1, by rw [← hux]; exact h2⟩
  -- 5. strict monotonicity below the wrap
  have hmono : ∀ i, i + 1 < m → a i < a (i + 1) := by
    intro i h
    have hi : i < m := Nat.lt_of_succ_lt h
    rw [hbelow i hi, hbelow (i+1) h]
    exact_mod_cast (e.lt_iff_lt.mpr (by simp [Fin.lt_def]))
  -- 6. a chosen neighbour realizing each argument
  have hrep : ∀ i, i < m → ∃ u ∈ D, θ u = a i := by
    intro i h
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp (hmem i h)
    exact ⟨u, hu, hux⟩
  choose! pt hptD hptθ using hrep
  -- 7. the gap bound, both regimes
  have hgap : ∀ i, i < m → Real.pi / 3 ≤ a (i + 1) - a i := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) m with hlt | hge
    · -- interior gap
      have hu := hptD i hi
      have hw := hptD (i+1) hlt
      have hne' : pt i ≠ pt (i+1) := by
        intro hEq
        have := hptθ i hi
        rw [hEq, hptθ (i+1) hlt] at this
        exact absurd this.symm (ne_of_lt (hmono i hlt))
      have h1 := o01_sixty_degree_gap v (pt i) (pt (i+1)) (hunit _ hu) (hunit _ hw)
        (hsep _ hu _ hw hne')
      obtain ⟨-, -, hc0, hc1⟩ := hθ (pt i) hu
      obtain ⟨-, -, hd0, hd1⟩ := hθ (pt (i+1)) hw
      rw [hptθ i hi] at hc0 hc1
      rw [hptθ (i+1) hlt] at hd0 hd1
      have hid := o02d_unit_chord_identity v (pt i) (pt (i+1)) (a i) (a (i+1)) hc0 hc1 hd0 hd1
      have h2 := o02c_angle_le_arg_gap v (pt i) (pt (i+1)) (a i) (a (i+1))
        (hunit _ hu) (hunit _ hw) hid o02b_arccos_cos_le_abs
      have hlt' := hmono i hlt
      rw [abs_of_nonpos (by linarith)] at h2
      linarith
    · -- the wrap gap: i + 1 = m
      have hEq : i + 1 = m := le_antisymm hi hge
      have hpi := Real.pi_pos
      rw [hEq, hwrap]
      rcases Nat.eq_or_lt_of_le hmpos with h1 | h1
      · -- m = 1, so i = 0 and the gap is the whole turn
        have : i = 0 := by omega
        rw [this]; linarith
      · -- m ≥ 2
        have hi0 : (0:ℕ) < m := hmpos
        have hipos : (0:ℕ) < i := by omega
        have hlt0i : a 0 < a i := by
          rw [hbelow 0 hi0, hbelow i hi]
          exact_mod_cast (e.lt_iff_lt.mpr (by simp [Fin.lt_def]; omega))
        have hne2 : pt i ≠ pt 0 := by
          intro hEq2
          have hz := hptθ 0 hi0
          have hthis := hptθ i hi
          rw [hEq2] at hthis
          exact absurd (hz.symm.trans hthis) (ne_of_lt hlt0i)
        have hu := hptD i hi
        have hw := hptD 0 hi0
        have h1' := o01_sixty_degree_gap v (pt i) (pt 0) (hunit _ hu) (hunit _ hw)
          (hsep _ hu _ hw hne2)
        obtain ⟨-, -, hc0, hc1⟩ := hθ (pt i) hu
        obtain ⟨-, -, hd0, hd1⟩ := hθ (pt 0) hw
        rw [hptθ i hi] at hc0 hc1
        rw [hptθ 0 hi0] at hd0 hd1
        have hd0' : (pt 0).ofLp 0 = v.ofLp 0 + Real.cos (a 0 + 2 * Real.pi) := by
          rw [Real.cos_add_two_pi]; exact hd0
        have hd1' : (pt 0).ofLp 1 = v.ofLp 1 + Real.sin (a 0 + 2 * Real.pi) := by
          rw [Real.sin_add_two_pi]; exact hd1
        have hid := o02d_unit_chord_identity v (pt i) (pt 0) (a i) (a 0 + 2 * Real.pi)
          hc0 hc1 hd0' hd1'
        have h2 := o02c_angle_le_arg_gap v (pt i) (pt 0) (a i) (a 0 + 2 * Real.pi)
          (hunit _ hu) (hunit _ hw) hid o02b_arccos_cos_le_abs
        have hbi := hbounds i hi
        have hb0 := hbounds 0 hi0
        rw [abs_of_nonpos (by linarith [hbi.2, hb0.1])] at h2
        linarith
  exact ⟨a, hbounds, hmono, hwrap, hgap, by
    rw [← hm] at *
    exact o02e_cyclic_gap_sum m a hwrap⟩

#print axioms o02_cyclic_angular_order_repaired
