import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

/-! # erdos:1084 upper -- S1, THE CONVEXITY OBLIGATION.  Core development.

S1 is the second half of the H3 decomposition: from a listing of hull VERTICES sorted by
polar argument about an interior point, produce the three cross-product signs that
`s2_sides_to_polar` (SEALED, `H3_S2_SidesToPolar.lean`) consumes.
-/

noncomputable def cross (a b c : ℝ^ 2) : ℝ :=
  (b.ofLp 0 - a.ofLp 0) * (c.ofLp 1 - a.ofLp 1)
    - (b.ofLp 1 - a.ofLp 1) * (c.ofLp 0 - a.ofLp 0)

/-! ## Coordinate plumbing -/

theorem sm0 (t : ℝ) (x : ℝ^ 2) : (t • x).ofLp 0 = t * x.ofLp 0 := rfl
theorem sm1 (t : ℝ) (x : ℝ^ 2) : (t • x).ofLp 1 = t * x.ofLp 1 := rfl
theorem ad0 (x y : ℝ^ 2) : (x + y).ofLp 0 = x.ofLp 0 + y.ofLp 0 := rfl
theorem ad1 (x y : ℝ^ 2) : (x + y).ofLp 1 = x.ofLp 1 + y.ofLp 1 := rfl

theorem pt_ext (x y : ℝ^ 2) (h0 : x.ofLp 0 = y.ofLp 0) (h1 : x.ofLp 1 = y.ofLp 1) :
    x = y := by
  ext k
  fin_cases k
  · exact h0
  · exact h1

/-! ## The algebraic core: CRAMER.

If the middle direction `m` sits inside the (salient) cone spanned by `u` and `w`, and the
turn at the middle point is NOT strictly right, then `m` is a convex combination of `0`,
`u` and `w` -- with strictly positive weights on `u` and `w`. -/
theorem cross_core (u0 u1 m0 m1 w0 w1 : ℝ)
    (hum : u0 * m1 - u1 * m0 < 0)
    (hmw : m0 * w1 - m1 * w0 < 0)
    (hneg : u0 * w1 - u1 * w0 < 0)
    (hcon : u0 * w1 - u1 * w0 - (u0 * m1 - u1 * m0) - (m0 * w1 - m1 * w0) ≤ 0) :
    ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ lam + mu ≤ 1 ∧
      m0 = lam * u0 + mu * w0 ∧ m1 = lam * u1 + mu * w1 := by
  have hDne : u0 * w1 - u1 * w0 ≠ 0 := ne_of_lt hneg
  obtain ⟨lam, mu, hc0, hc1⟩ :
      ∃ lam mu : ℝ, m0 = lam * u0 + mu * w0 ∧ m1 = lam * u1 + mu * w1 :=
    ⟨(m0 * w1 - m1 * w0) / (u0 * w1 - u1 * w0),
     (u0 * m1 - u1 * m0) / (u0 * w1 - u1 * w0),
     by rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hDne]; ring,
     by rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hDne]; ring⟩
  have huxm : u0 * m1 - u1 * m0 = mu * (u0 * w1 - u1 * w0) := by
    rw [hc0, hc1]; ring
  have hmxw : m0 * w1 - m1 * w0 = lam * (u0 * w1 - u1 * w0) := by
    rw [hc0, hc1]; ring
  have hlam : 0 < lam := by
    by_contra hx
    push_neg at hx
    have hh := mul_nonneg (neg_nonneg.2 hx) (neg_nonneg.2 hneg.le)
    nlinarith [hh, hmxw, hmw]
  have hmu : 0 < mu := by
    by_contra hx
    push_neg at hx
    have hh := mul_nonneg (neg_nonneg.2 hx) (neg_nonneg.2 hneg.le)
    nlinarith [hh, huxm, hum]
  have hsum : lam + mu ≤ 1 := by
    by_contra hx
    push_neg at hx
    have hh := mul_pos (sub_pos.2 hx) (neg_pos.2 hneg)
    nlinarith [hh, huxm, hmxw, hcon]
  exact ⟨lam, mu, hlam, hmu, hsum, hc0, hc1⟩

/-! ## The geometric core: an extreme point is not an interior convex combination. -/

theorem extreme_combo_absurd
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (v₀ X Z Y : ℝ^ 2)
    (hv : v₀ ∈ A) (hX : X ∈ A) (hZ : Z ∈ A) (hYe : Y ∈ A.extremePoints ℝ)
    (hYv : Y ≠ v₀) (hYX : Y ≠ X)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hsum : lam + mu ≤ 1)
    (hrep : Y = (1 - (lam + mu)) • v₀ + (lam • X + mu • Z)) : False := by
  have hs0 : (0 : ℝ) < lam + mu := by linarith
  have hsne : lam + mu ≠ 0 := ne_of_gt hs0
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ^ 2,
      c = (lam / (lam + mu)) • X + (mu / (lam + mu)) • Z := ⟨_, rfl⟩
  have hsum1 : lam / (lam + mu) + mu / (lam + mu) = 1 := by
    rw [← add_div]; exact div_self hsne
  have hcA : c ∈ A := by
    rw [hcdef]
    exact hA.segment_subset hX hZ
      ⟨lam / (lam + mu), mu / (lam + mu), div_nonneg hlam.le hs0.le,
        div_nonneg hmu.le hs0.le, hsum1, rfl⟩
  have e1 : (lam + mu) * (lam / (lam + mu)) = lam := by field_simp
  have e2 : (lam + mu) * (mu / (lam + mu)) = mu := by field_simp
  have hsc : (1 - (lam + mu)) • v₀ + (lam + mu) • c = Y := by
    rw [hcdef, hrep, smul_add, smul_smul, smul_smul, e1, e2]
  rcases lt_or_eq_of_le hsum with hlt1 | heq1
  · exact hYv ((mem_extremePoints.mp hYe).2 v₀ hv c hcA
      ⟨1 - (lam + mu), lam + mu, by linarith, hs0, by ring, hsc⟩).1.symm
  · have hYc : Y = c := by
      rw [← hsc, heq1]; simp
    have hmem : Y ∈ openSegment ℝ X Z := by
      refine ⟨lam / (lam + mu), mu / (lam + mu), div_pos hlam hs0, div_pos hmu hs0,
        hsum1, ?_⟩
      rw [← hcdef, ← hYc]
    exact hYX ((mem_extremePoints.mp hYe).2 X hX Z hZ hmem).1.symm

/-! ## S1, PROVED. -/

theorem s1_consecutive_signs
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ A)
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hext : ∀ i, p i ∈ A.extremePoints ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi)
    (i : ℕ) :
    0 < cross (p (i + 1)) (p i) (p (i + 2)) ∧
    0 < cross (p (i + 1)) (p i) v₀ * cross (p (i + 1)) (p i) (p (i + 2)) ∧
    0 < cross (p (i + 1)) (p (i + 2)) v₀ * cross (p (i + 1)) (p (i + 2)) (p i) := by
  -- the two consecutive central gaps are strictly between 0 and π, so their sines are
  -- positive and the two adjacent planar cross products about v₀ are strictly negative
  have hum : r i * Real.cos (a i) * (r (i + 1) * Real.sin (a (i + 1)))
      - r i * Real.sin (a i) * (r (i + 1) * Real.cos (a (i + 1))) < 0 := by
    have hs : 0 < Real.sin (a i - a (i + 1)) :=
      Real.sin_pos_of_pos_of_lt_pi (hpos i) (hlt i)
    have hid : r i * Real.cos (a i) * (r (i + 1) * Real.sin (a (i + 1)))
        - r i * Real.sin (a i) * (r (i + 1) * Real.cos (a (i + 1)))
        = -(r i * r (i + 1) * Real.sin (a i - a (i + 1))) := by
      rw [Real.sin_sub]; ring
    have hp := mul_pos (mul_pos (hr i) (hr (i + 1))) hs
    rw [hid]; linarith
  have hmw : r (i + 1) * Real.cos (a (i + 1)) * (r (i + 2) * Real.sin (a (i + 2)))
      - r (i + 1) * Real.sin (a (i + 1)) * (r (i + 2) * Real.cos (a (i + 2))) < 0 := by
    have hs : 0 < Real.sin (a (i + 1) - a (i + 2)) :=
      Real.sin_pos_of_pos_of_lt_pi (hpos (i + 1)) (hlt (i + 1))
    have hid : r (i + 1) * Real.cos (a (i + 1)) * (r (i + 2) * Real.sin (a (i + 2)))
        - r (i + 1) * Real.sin (a (i + 1)) * (r (i + 2) * Real.cos (a (i + 2)))
        = -(r (i + 1) * r (i + 2) * Real.sin (a (i + 1) - a (i + 2))) := by
      rw [Real.sin_sub]; ring
    have hp := mul_pos (mul_pos (hr (i + 1)) (hr (i + 2))) hs
    rw [hid]; linarith
  -- the four cross products, in polar coordinates about v₀
  have E1 : cross (p (i + 1)) (p i) v₀
      = -(r i * Real.cos (a i) * (r (i + 1) * Real.sin (a (i + 1)))
          - r i * Real.sin (a i) * (r (i + 1) * Real.cos (a (i + 1)))) := by
    simp only [cross, hp0, hp1]; ring
  have E2 : cross (p (i + 1)) (p (i + 2)) v₀
      = r (i + 1) * Real.cos (a (i + 1)) * (r (i + 2) * Real.sin (a (i + 2)))
        - r (i + 1) * Real.sin (a (i + 1)) * (r (i + 2) * Real.cos (a (i + 2))) := by
    simp only [cross, hp0, hp1]; ring
  have E3 : cross (p (i + 1)) (p i) (p (i + 2))
      = r i * Real.cos (a i) * (r (i + 2) * Real.sin (a (i + 2)))
          - r i * Real.sin (a i) * (r (i + 2) * Real.cos (a (i + 2)))
        - (r i * Real.cos (a i) * (r (i + 1) * Real.sin (a (i + 1)))
          - r i * Real.sin (a i) * (r (i + 1) * Real.cos (a (i + 1))))
        - (r (i + 1) * Real.cos (a (i + 1)) * (r (i + 2) * Real.sin (a (i + 2)))
          - r (i + 1) * Real.sin (a (i + 1)) * (r (i + 2) * Real.cos (a (i + 2)))) := by
    simp only [cross, hp0, hp1]; ring
  have E4 : cross (p (i + 1)) (p (i + 2)) (p i)
      = -(r i * Real.cos (a i) * (r (i + 2) * Real.sin (a (i + 2)))
          - r i * Real.sin (a i) * (r (i + 2) * Real.cos (a (i + 2)))
        - (r i * Real.cos (a i) * (r (i + 1) * Real.sin (a (i + 1)))
          - r i * Real.sin (a i) * (r (i + 1) * Real.cos (a (i + 1))))
        - (r (i + 1) * Real.cos (a (i + 1)) * (r (i + 2) * Real.sin (a (i + 2)))
          - r (i + 1) * Real.sin (a (i + 1)) * (r (i + 2) * Real.cos (a (i + 2))))) := by
    simp only [cross, hp0, hp1]; ring
  -- THE TURN AT p (i+1) IS STRICTLY RIGHT.  This is the whole geometric content.
  have HOR : 0 < cross (p (i + 1)) (p i) (p (i + 2)) := by
    rw [E3]
    by_cases hD : (0 : ℝ) ≤ r i * Real.cos (a i) * (r (i + 2) * Real.sin (a (i + 2)))
        - r i * Real.sin (a i) * (r (i + 2) * Real.cos (a (i + 2)))
    · linarith
    · push_neg at hD
      by_contra hcon
      push_neg at hcon
      obtain ⟨lam, mu, hlam, hmu, hsum, hc0, hc1⟩ :=
        cross_core (r i * Real.cos (a i)) (r i * Real.sin (a i))
          (r (i + 1) * Real.cos (a (i + 1))) (r (i + 1) * Real.sin (a (i + 1)))
          (r (i + 2) * Real.cos (a (i + 2))) (r (i + 2) * Real.sin (a (i + 2)))
          hum hmw hD hcon
      have hYv : p (i + 1) ≠ v₀ := by
        intro hEq
        have h0 : r (i + 1) * Real.cos (a (i + 1)) = 0 := by
          have hx := hp0 (i + 1); rw [hEq] at hx; linarith
        have h1 : r (i + 1) * Real.sin (a (i + 1)) = 0 := by
          have hx := hp1 (i + 1); rw [hEq] at hx; linarith
        rw [h0, h1] at hum
        linarith
      have hYX : p (i + 1) ≠ p i := by
        intro hEq
        have h0 : r i * Real.cos (a i) = r (i + 1) * Real.cos (a (i + 1)) := by
          have e1 := hp0 i
          have e2 := hp0 (i + 1)
          rw [hEq] at e2
          linarith
        have h1 : r i * Real.sin (a i) = r (i + 1) * Real.sin (a (i + 1)) := by
          have e1 := hp1 i
          have e2 := hp1 (i + 1)
          rw [hEq] at e2
          linarith
        rw [← h0, ← h1] at hum
        linarith
      have hrep : p (i + 1)
          = (1 - (lam + mu)) • v₀ + (lam • p i + mu • p (i + 2)) := by
        refine pt_ext _ _ ?_ ?_
        · simp only [ad0, sm0, hp0]
          linear_combination hc0
        · simp only [ad1, sm1, hp1]
          linear_combination hc1
      exact extreme_combo_absurd A hA v₀ (p i) (p (i + 2)) (p (i + 1)) hv₀
        (extremePoints_subset (hext i)) (extremePoints_subset (hext (i + 2)))
        (hext (i + 1)) hYv hYX lam mu hlam hmu hsum hrep
  refine ⟨HOR, ?_, ?_⟩
  · rw [E1]
    rw [E3] at HOR
    rw [E3]
    nlinarith [hum, HOR]
  · rw [E2, E4]
    rw [E3] at HOR
    nlinarith [hmw, HOR]

#print axioms s1_consecutive_signs
