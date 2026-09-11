
/-! ## H05_Assembly, REPRODUCED VERBATIM (namespace dropped so it shares these definitions). -/

noncomputable def nbrs (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : Finset (ℝ^ 2) :=
  {u ∈ S | dist v u = 1}

noncomputable def udeg (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : ℕ := (nbrs S v).card

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

theorem sum_bound_degenerate (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (hH1 : ∀ v ∈ S, udeg S v ≤ 2) :
    (∑ v ∈ hullPts S, (udeg S v : ℝ)) ≤ 4 * h - 6 := by
  have hsub : ∀ v ∈ hullPts S, (udeg S v : ℝ) ≤ 2 := by
    intro v hv
    have hvS : v ∈ S := (mem_hullPts_iff.mp hv).1
    exact_mod_cast hH1 v hvS
  have hcast : (3 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h3
  calc (∑ v ∈ hullPts S, (udeg S v : ℝ))
      ≤ ∑ _v ∈ hullPts S, (2 : ℝ) := Finset.sum_le_sum hsub
    _ = 2 * h := by
        rw [Finset.sum_const, ← hh]
        simp [nsmul_eq_mul, mul_comm]
    _ ≤ 4 * h - 6 := by linarith

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
    · intro c hc
      exact hmem c (Finset.mem_range.mp hc)
    · intro c hc d hd hcd
      exact hinj c (Finset.mem_range.mp hc) d (Finset.mem_range.mp hd) hcd
    · intro w hw
      obtain ⟨i, hi, hpi'⟩ := hsurj w hw
      exact ⟨i, Finset.mem_range.mpr hi, hpi'⟩
    · intro c _
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

theorem hull_angle_package_pre (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (hbranch : (∀ v ∈ S, udeg S v ≤ 2) ∨ FanInterface S h) :
    ∃ alpha : ℝ^ 2 → ℝ,
      (∀ v ∈ hullPts S, (udeg S v : ℝ) ≤ 1 + 3 * alpha v / Real.pi) ∧
      (∑ v ∈ hullPts S, alpha v = ((h : ℝ) - 2) * Real.pi) :=
  package_of_sum_bound S h hh h3
    (hbranch.elim (sum_bound_degenerate S h hh h3) (sum_bound_of_fan S h hh h3))

/-! ## NEW: the gap data is CLOSED under the period, and the `2π` central total is FREE. -/

theorem gap_periodic (a : ℕ → ℝ) (h : ℕ)
    (hpera : ∀ i, a (i + h) = a i - 2 * Real.pi) :
    ∀ n i, a (i + n * h) - a (i + n * h + 1) = a i - a (i + 1) := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    have e1 : i + (m + 1) * h = i + m * h + h := by ring
    have e2 : i + m * h + h + 1 = (i + m * h + 1) + h := by ring
    rw [e1, e2, hpera (i + m * h), hpera (i + m * h + 1)]
    have hih := ih i
    linarith

theorem gap_sum_of_period (a : ℕ → ℝ) (h : ℕ)
    (hpera : ∀ i, a (i + h) = a i - 2 * Real.pi) :
    ∑ i ∈ Finset.range h, (a i - a (i + 1)) = 2 * Real.pi := by
  have tel : ∀ n : ℕ, ∑ i ∈ Finset.range n, (a i - a (i + 1)) = a 0 - a n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  rw [tel h]
  have hz : a h = a 0 - 2 * Real.pi := by simpa using hpera 0
  rw [hz]; ring

/-! ## NEW: THE FAN INTERFACE, PRODUCED. -/

/-- The polar description of a closed hull listing about an INTERIOR centre, plus the
per-vertex packing bound.  Every other clause of `FanInterface` is derived from this. -/
def PolarFan (S : Finset (ℝ^ 2)) (h : ℕ) : Prop :=
  ∃ (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ) (v₀ : ℝ^ 2),
    v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))) ∧
    (∀ i, p i ∈ hullPts S) ∧
    (∀ w ∈ hullPts S, ∃ i < h, p (i + 1) = w) ∧
    (∀ i < h, ∀ j < h, p (i + 1) = p (j + 1) → i = j) ∧
    (∀ i, p (i + h) = p i) ∧
    (∀ i, a (i + h) = a i - 2 * Real.pi) ∧
    (∀ i, 0 < r i) ∧
    (∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i)) ∧
    (∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i)) ∧
    (∀ i, 0 < a i - a (i + 1)) ∧
    (∀ i < h, (udeg S (p (i + 1)) : ℝ)
      ≤ 1 + 3 * EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2)) / Real.pi)

/-- ⛔ THE PRODUCTION.  `FanInterface` -- whose angle-sum clause `H05` could only ASSUME --
now follows from the polar listing alone.  The gap ceiling is discharged at every index by
gap 2 plus the period; the `2π` central total by telescoping. -/
theorem fanInterface_of_polarFan (S : Finset (ℝ^ 2)) (h : ℕ) (hh : 3 ≤ h)
    (hpf : PolarFan S h) : FanInterface S h := by
  obtain ⟨p, a, r, v₀, hv₀, hmem, hsurj, hinj, hper, hpera, hr, hp0, hp1, hpos, hpack⟩ := hpf
  have hbase : ∀ k, k < h → a k - a (k + 1) < Real.pi := fun k hk =>
    gap_lt_pi_hullPts S h v₀ hv₀ p a r hr hp0 hp1 hpos hper hpera hsurj k hk
  have hlt : ∀ k, a k - a (k + 1) < Real.pi := by
    intro k
    have hh0 : 0 < h := by omega
    have hmod : k % h < h := Nat.mod_lt _ hh0
    have hgp := gap_periodic a h hpera (k / h) (k % h)
    rw [Nat.mod_add_div' k h] at hgp
    rw [hgp]
    exact hbase (k % h) hmod
  refine ⟨p, fun i _ => hmem (i + 1), hsurj, hinj, ?_, hpack⟩
  exact e1084_hullPts_angle_sum S h hh v₀ hv₀ p a r hmem hper hr hp0 hp1 hpos hlt
    (gap_sum_of_period a h hpera)

/-- ⛔ THE PACKAGE, FROM THE POLAR LISTING.  Compare `hull_angle_package_pre`, whose fan
branch demanded an ASSUMED interior-angle sum: this one demands only the listing and the
per-vertex packing bound. -/
theorem hull_angle_package_of_polar (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h)
    (hbranch : (∀ v ∈ S, udeg S v ≤ 2) ∨ PolarFan S h) :
    ∃ alpha : ℝ^ 2 → ℝ,
      (∀ v ∈ hullPts S, (udeg S v : ℝ) ≤ 1 + 3 * alpha v / Real.pi) ∧
      (∑ v ∈ hullPts S, alpha v = ((h : ℝ) - 2) * Real.pi) :=
  hull_angle_package_pre S h hh h3
    (hbranch.imp id (fun hpf => fanInterface_of_polarFan S h h3 hpf))

#print axioms e1084_hullPts_angle_sum
#print axioms gap_lt_pi_hullPts
#print axioms gap_sum_of_period
#print axioms fanInterface_of_polarFan
#print axioms hull_angle_package_pre
#print axioms hull_angle_package_of_polar
