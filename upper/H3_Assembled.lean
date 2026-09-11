import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open Complex

/-! # erdos:1084 upper -- H3 ASSEMBLED, AND SPLICED INTO THE FAN ANGLE SUM.

Three layers, one file, no `sorry`:

* **S2** (`s2_sides_to_polar`) -- VERBATIM from `H3_S2_SidesToPolar.lean`, already sealed.
* **S1** (`s1_consecutive_signs`) -- the convexity obligation, PROVED here.
* **H3** (`h3_hull_inside`) -- their composition: a listing of hull VERTICES sorted by
  descending polar argument about an interior point satisfies `InsideAngleAt` at every
  index.
* **THE SPLICE** (`e1084_hull_angle_sum`) -- H3 fed into the sealed descending handoff
  `o06_angle_sum_of_polar_fan_desc` (reproduced here from `O06_PolarFan_Handoff_Desc.lean`):
  the interior angles of a hull-vertex listing sum to `(h-2)π`, with NO assumed angle
  identity and NO assumed cone containment.

⛔ THREE STATEMENT DEFECTS IN THE FROZEN S1 (`H3_Decomposition_SCAFFOLD.lean`), all
repaired here; see `S1-REPORT-2026-09-05.md` beside this file.
-/

/-! ## Shared definitions (verbatim across the campaign) -/

noncomputable def toC (q : ℝ^ 2) : ℂ := ⟨q.ofLp 0, q.ofLp 1⟩

noncomputable def cross (a b c : ℝ^ 2) : ℝ :=
  (b.ofLp 0 - a.ofLp 0) * (c.ofLp 1 - a.ofLp 1)
    - (b.ofLp 1 - a.ofLp 1) * (c.ofLp 0 - a.ofLp 0)

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

/-! ## S2 -- VERBATIM from the sealed `H3_S2_SidesToPolar.lean`. -/

/-- `x` is an argument of `z`: it need not be `arg z`, only congruent to it. -/
def IsArg (x : ℝ) (z : ℂ) : Prop :=
  Real.cos x = z.re / ‖z‖ ∧ Real.sin x = z.im / ‖z‖

theorem isArg_arg {z : ℂ} (hz : z ≠ 0) : IsArg z.arg z :=
  ⟨Complex.cos_arg hz, Complex.sin_arg z⟩

theorem isArg_add {x : ℝ} {z c : ℂ} (hz : z ≠ 0) (hc : c ≠ 0) (h : IsArg x z) :
    IsArg (x + c.arg) (z * c) := by
  obtain ⟨hcos, hsin⟩ := h
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  constructor
  · rw [Real.cos_add, hcos, hsin, Complex.cos_arg hc, Complex.sin_arg,
        Complex.mul_re, norm_mul]
    field_simp
  · rw [Real.sin_add, hcos, hsin, Complex.cos_arg hc, Complex.sin_arg,
        Complex.mul_im, norm_mul]
    field_simp
    ring

theorem arg_mem_Ioo {z : ℂ} (h : 0 < z.im) : 0 < z.arg ∧ z.arg < Real.pi := by
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le) ?_, ?_⟩
  · intro hEq
    have := (Complex.arg_eq_zero_iff.mp hEq.symm).2
    linarith
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt h))

theorem im_div (z c : ℂ) :
    (z / c).im = (c.re * z.im - c.im * z.re) / Complex.normSq c := by
  rw [Complex.div_im]
  ring

theorem toC_sub_re (a b : ℝ^ 2) : (toC a - toC b).re = a.ofLp 0 - b.ofLp 0 := rfl
theorem toC_sub_im (a b : ℝ^ 2) : (toC a - toC b).im = a.ofLp 1 - b.ofLp 1 := rfl

/-- S2, PROVED. -/
theorem s2_sides_to_polar (v X Y Z : ℝ^ 2)
    (hor : 0 < cross Y X Z)
    (h1 : 0 < cross Y X v * cross Y X Z)
    (h2 : 0 < cross Y Z v * cross Y Z X)
    (p : ℕ → ℝ^ 2) (i : ℕ) (hpi : p i = X) (hpi1 : p (i + 1) = Y) (hpi2 : p (i + 2) = Z) :
    InsideAngleAt v p i := by
  set u : ℂ := toC X - toC Y with hu
  set t : ℂ := toC v - toC Y with ht
  set w : ℂ := toC Z - toC Y with hw
  have cXZ : cross Y X Z = u.re * w.im - u.im * w.re := by
    simp only [cross, hu, hw, toC_sub_re, toC_sub_im]
  have cXv : cross Y X v = u.re * t.im - u.im * t.re := by
    simp only [cross, hu, ht, toC_sub_re, toC_sub_im]
  have cZv : cross Y Z v = w.re * t.im - w.im * t.re := by
    simp only [cross, hw, ht, toC_sub_re, toC_sub_im]
  have cZX : cross Y Z X = -(u.re * w.im - u.im * w.re) := by
    simp only [cross, hw, hu, toC_sub_re, toC_sub_im]; ring
  rw [cXZ] at hor
  rw [cXv, cXZ] at h1
  rw [cZv, cZX] at h2
  have hut : 0 < u.re * t.im - u.im * t.re := by nlinarith
  have htw : 0 < t.re * w.im - t.im * w.re := by nlinarith
  have hu0 : u ≠ 0 := by
    intro hz; rw [hz] at hor; simp at hor
  have hw0 : w ≠ 0 := by
    intro hz; rw [hz] at hor; simp at hor
  have ht0 : t ≠ 0 := by
    intro hz; rw [hz] at hut; simp at hut
  have hnu : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu0
  have hnt : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
  have him1 : 0 < (t / u).im := by
    rw [im_div]; exact div_pos hut hnu
  have him2 : 0 < (w / t).im := by
    rw [im_div]; exact div_pos htw hnt
  have him3 : 0 < (w / u).im := by
    rw [im_div]; exact div_pos hor hnu
  obtain ⟨hp1, hq1⟩ := arg_mem_Ioo him1
  obtain ⟨hp2, hq2⟩ := arg_mem_Ioo him2
  set α : ℝ := u.arg with hα
  set β : ℝ := α + (t / u).arg with hβ
  set γ : ℝ := β + (w / t).arg with hγ
  have hdu : t / u ≠ 0 := div_ne_zero ht0 hu0
  have hdt : w / t ≠ 0 := div_ne_zero hw0 ht0
  have hA : IsArg α u := isArg_arg hu0
  have hB : IsArg β t := by
    have := isArg_add hu0 hdu hA
    rwa [mul_div_cancel₀ _ hu0] at this
  have hC : IsArg γ w := by
    have := isArg_add ht0 hdt hB
    rwa [mul_div_cancel₀ _ ht0] at this
  have htot : γ - α ≤ Real.pi := by
    by_contra hgt
    push_neg at hgt
    have hArg : IsArg ((t / u).arg + (w / t).arg) ((t / u) * (w / t)) :=
      isArg_add hdu hdt (isArg_arg hdu)
    have hmul : (t / u) * (w / t) = w / u := by
      field_simp
    rw [hmul] at hArg
    have hsinpos : 0 < Real.sin ((t / u).arg + (w / t).arg) := by
      rw [hArg.2]
      exact div_pos him3 (norm_pos_iff.mpr (div_ne_zero hw0 hu0))
    have hsum : (t / u).arg + (w / t).arg = γ - α := by simp only [hγ, hβ]; ring
    rw [hsum] at hsinpos
    have hlt2pi : γ - α < 2 * Real.pi := by simp only [hγ, hβ]; linarith
    have h0 : 0 < γ - α - Real.pi := by linarith
    have h1' : γ - α - Real.pi < Real.pi := by linarith
    have hpos := Real.sin_pos_of_pos_of_lt_pi h0 h1'
    have heq : Real.sin (γ - α) = -Real.sin (γ - α - Real.pi) := by
      rw [show γ - α = (γ - α - Real.pi) + Real.pi by ring, Real.sin_add_pi]
      ring_nf
    rw [heq] at hsinpos
    linarith
  refine ⟨α, β, γ, ‖u‖, ‖t‖, ‖w‖,
    norm_pos_iff.mpr hu0, norm_pos_iff.mpr ht0, norm_pos_iff.mpr hw0, ?_, ?_, ?_, ?_, ?_, ?_,
    by simp only [hβ]; linarith, by simp only [hβ]; linarith,
    by simp only [hγ]; linarith, by simp only [hγ]; linarith, htot⟩
  · rw [hpi, hpi1, hA.1]
    field_simp
    have : u.re = X.ofLp 0 - Y.ofLp 0 := rfl
    linarith
  · rw [hpi, hpi1, hA.2]
    field_simp
    have : u.im = X.ofLp 1 - Y.ofLp 1 := rfl
    linarith
  · rw [hpi1, hB.1]
    field_simp
    have : t.re = v.ofLp 0 - Y.ofLp 0 := rfl
    linarith
  · rw [hpi1, hB.2]
    field_simp
    have : t.im = v.ofLp 1 - Y.ofLp 1 := rfl
    linarith
  · rw [hpi2, hpi1, hC.1]
    field_simp
    have : w.re = Z.ofLp 0 - Y.ofLp 0 := rfl
    linarith
  · rw [hpi2, hpi1, hC.2]
    field_simp
    have : w.im = Z.ofLp 1 - Y.ofLp 1 := rfl
    linarith

/-! ## S1 -- THE CONVEXITY OBLIGATION.  Coordinate plumbing first. -/

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

/-- CRAMER.  If the middle direction sits inside the salient cone spanned by the outer two
and the turn at the middle point is not strictly right, the middle point is a convex
combination of the centre and the two outer points, with strictly positive outer weights. -/
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

/-- An extreme point of a convex set is not an interior convex combination of three of its
points with positive weight on two of them. -/
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

/-- ⛔ S1, PROVED.  For a listing of EXTREME points of a convex set `A`, described in polar
coordinates about a point `v₀ ∈ A` with strictly descending arguments and every consecutive
gap strictly below `π`, the three cross-product signs that `s2_sides_to_polar` consumes all
hold at every index. -/
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

/-! ## H3 -- S1 composed with S2. -/

/-- ⛔ H3, PROVED.  A listing of EXTREME points of a convex set `A`, sorted by strictly
descending polar argument about a point `v₀ ∈ A` with every consecutive central gap
strictly below `π`, puts `v₀` inside the angle at every vertex. -/
theorem h3_hull_inside
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ A)
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hext : ∀ i, p i ∈ A.extremePoints ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi) :
    ∀ i, InsideAngleAt v₀ p i := by
  intro i
  obtain ⟨hor, hh1, hh2⟩ :=
    s1_consecutive_signs A hA v₀ hv₀ p a r hext hr hp0 hp1 hpos hlt i
  exact s2_sides_to_polar v₀ (p i) (p (i + 1)) (p (i + 2)) hor hh1 hh2 p i rfl rfl rfl

/-! ## The descending handoff, reproduced from the sealed `O06_PolarFan_Handoff_Desc.lean`. -/

theorem polar_angle_eq_arccos_cos (v u w : ℝ^ 2) (a b ru rw : ℝ)
    (hru : 0 < ru) (hrw : 0 < rw)
    (hu0 : u.ofLp 0 = v.ofLp 0 + ru * Real.cos a) (hu1 : u.ofLp 1 = v.ofLp 1 + ru * Real.sin a)
    (hw0 : w.ofLp 0 = v.ofLp 0 + rw * Real.cos b) (hw1 : w.ofLp 1 = v.ofLp 1 + rw * Real.sin b) :
    EuclideanGeometry.angle u v w = Real.arccos (Real.cos (a - b)) := by
  have hsa : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  have hsb : Real.sin b ^ 2 + Real.cos b ^ 2 = 1 := Real.sin_sq_add_cos_sq b
  rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
  congr 1
  have hinner : (inner ℝ (u -ᵥ v) (w -ᵥ v) : ℝ) = ru * rw * Real.cos (a - b) := by
    simp [inner, Fin.sum_univ_two, vsub_eq_sub, hu0, hu1, hw0, hw1, Real.cos_sub]
    ring
  have hnu : ‖u -ᵥ v‖ = ru := by
    rw [EuclideanSpace.norm_eq]
    simp only [vsub_eq_sub, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    rw [show (u - v).ofLp 0 ^ 2 + (u - v).ofLp 1 ^ 2 = ru ^ 2 by
      simp [hu0, hu1]; nlinarith [hsa]]
    exact Real.sqrt_sq hru.le
  have hnw : ‖w -ᵥ v‖ = rw := by
    rw [EuclideanSpace.norm_eq]
    simp only [vsub_eq_sub, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    rw [show (w - v).ofLp 0 ^ 2 + (w - v).ofLp 1 ^ 2 = rw ^ 2 by
      simp [hw0, hw1]; nlinarith [hsb]]
    exact Real.sqrt_sq hrw.le
  rw [hinner, hnu, hnw]
  field_simp

theorem arccos_cos_of_nonneg_le_pi (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ Real.pi) :
    Real.arccos (Real.cos t) = t := Real.arccos_cos h0 h1

theorem polar_angle_add (v u y w : ℝ^ 2) (a b c ru ry rw : ℝ)
    (hru : 0 < ru) (hry : 0 < ry) (hrw : 0 < rw)
    (hu0 : u.ofLp 0 = v.ofLp 0 + ru * Real.cos a) (hu1 : u.ofLp 1 = v.ofLp 1 + ru * Real.sin a)
    (hy0 : y.ofLp 0 = v.ofLp 0 + ry * Real.cos b) (hy1 : y.ofLp 1 = v.ofLp 1 + ry * Real.sin b)
    (hw0 : w.ofLp 0 = v.ofLp 0 + rw * Real.cos c) (hw1 : w.ofLp 1 = v.ofLp 1 + rw * Real.sin c)
    (hab : 0 ≤ b - a) (hab' : b - a ≤ Real.pi)
    (hbc : 0 ≤ c - b) (hbc' : c - b ≤ Real.pi)
    (hac' : c - a ≤ Real.pi) :
    EuclideanGeometry.angle u v y + EuclideanGeometry.angle y v w
      = EuclideanGeometry.angle u v w := by
  have e1 := polar_angle_eq_arccos_cos v u y a b ru ry hru hry hu0 hu1 hy0 hy1
  have e2 := polar_angle_eq_arccos_cos v y w b c ry rw hry hrw hy0 hy1 hw0 hw1
  have e3 := polar_angle_eq_arccos_cos v u w a c ru rw hru hrw hu0 hu1 hw0 hw1
  have c1 : Real.cos (a - b) = Real.cos (b - a) := by
    rw [show a - b = -(b - a) by ring, Real.cos_neg]
  have c2 : Real.cos (b - c) = Real.cos (c - b) := by
    rw [show b - c = -(c - b) by ring, Real.cos_neg]
  have c3 : Real.cos (a - c) = Real.cos (c - a) := by
    rw [show a - c = -(c - a) by ring, Real.cos_neg]
  rw [e1, e2, e3, c1, c2, c3,
      arccos_cos_of_nonneg_le_pi _ hab hab',
      arccos_cos_of_nonneg_le_pi _ hbc hbc',
      arccos_cos_of_nonneg_le_pi _ (by linarith) hac']
  ring

theorem o06_fan_angle_sum (h : ℕ) (hh : 3 ≤ h) (v : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (hper : ∀ i, p (i + h) = p i)
    (hvne : ∀ i, v ≠ p i)
    (hcentral : ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1))
        = 2 * Real.pi)
    (hadd : ∀ i, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
        = EuclideanGeometry.angle (p i) (p (i + 1)) v
          + EuclideanGeometry.angle v (p (i + 1)) (p (i + 2))) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi := by
  set b : ℕ → ℝ := fun i => EuclideanGeometry.angle v (p (i + 1)) (p i) with hb
  set g : ℕ → ℝ := fun i => EuclideanGeometry.angle (p (i + 1)) (p i) v with hg
  have tri : ∀ i, EuclideanGeometry.angle (p i) v (p (i + 1)) + b i + g i = Real.pi := by
    intro i
    simpa [hb, hg] using
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := p i) (p₂ := v)
        (p (i + 1)) (hvne i)
  have hsum : (∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1)))
      + (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g i) = (h : ℝ) * Real.pi := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp [tri, Finset.sum_const, Finset.card_range, mul_comm]
  have hgper : g h = g 0 := by
    have h1 : p (0 + h) = p 0 := hper 0
    have h2 : p (1 + h) = p 1 := hper 1
    simp only [hg]
    rw [show h + 1 = 1 + h by ring, h2, show h = 0 + h by ring, h1]
  have hshift : ∑ i ∈ Finset.range h, g (i + 1) = ∑ i ∈ Finset.range h, g i := by
    have e1 : ∑ i ∈ Finset.range (h + 1), g i
        = (∑ i ∈ Finset.range h, g (i + 1)) + g 0 := Finset.sum_range_succ' g h
    have e2 : ∑ i ∈ Finset.range (h + 1), g i
        = (∑ i ∈ Finset.range h, g i) + g h := Finset.sum_range_succ g h
    rw [hgper] at e2
    linarith [e1, e2]
  have hsplit : ∀ i, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = b i + g (i + 1) := by
    intro i
    rw [hadd i]
    congr 1
    · simpa [hb] using EuclideanGeometry.angle_comm (p i) (p (i + 1)) v
    · simpa [hg, add_assoc] using EuclideanGeometry.angle_comm v (p (i + 1)) (p (i + 2))
  calc ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ∑ i ∈ Finset.range h, (b i + g (i + 1)) := by
        exact Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g (i + 1)) :=
        Finset.sum_add_distrib
    _ = (∑ i ∈ Finset.range h, b i) + (∑ i ∈ Finset.range h, g i) := by rw [hshift]
    _ = ((h : ℝ) - 2) * Real.pi := by rw [hcentral] at hsum; linarith

theorem hadd_of_inside (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (i : ℕ) (h : InsideAngleAt v p i) :
    EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = EuclideanGeometry.angle (p i) (p (i + 1)) v
        + EuclideanGeometry.angle v (p (i + 1)) (p (i + 2)) := by
  obtain ⟨α, β, γ, r₁, r₂, r₃, h₁, h₂, h₃, e1, e2, e3, e4, e5, e6, b1, b2, b3, b4, b5⟩ := h
  exact (polar_angle_add (p (i + 1)) (p i) v (p (i + 2)) α β γ r₁ r₂ r₃
    h₁ h₂ h₃ e1 e2 e3 e4 e5 e6 b1 b2 b3 b4 b5).symm

theorem o06_angle_sum_of_interior_point (h : ℕ) (hh : 3 ≤ h) (v : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (hper : ∀ i, p (i + h) = p i)
    (hvne : ∀ i, v ≠ p i)
    (hcentral : ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) v (p (i + 1))
        = 2 * Real.pi)
    (hinside : ∀ i, InsideAngleAt v p i) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi :=
  o06_fan_angle_sum h hh v p hper hvne hcentral (fun i => hadd_of_inside v p i (hinside i))

theorem ne_of_pos_radius (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v.ofLp 1 + r i * Real.sin (a i)) :
    ∀ i, v ≠ p i := by
  intro i hEq
  have e0 : r i * Real.cos (a i) = 0 := by have := hp0 i; rw [← hEq] at this; linarith
  have e1 : r i * Real.sin (a i) = 0 := by have := hp1 i; rw [← hEq] at this; linarith
  have hri := (hr i).ne'
  have hc : Real.cos (a i) = 0 := by
    rcases mul_eq_zero.mp e0 with h | h
    · exact absurd h hri
    · exact h
  have hs : Real.sin (a i) = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h hri
    · exact h
  have := Real.sin_sq_add_cos_sq (a i)
  rw [hc, hs] at this
  norm_num at this

theorem hcentral_of_polar_desc (m : ℕ) (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v.ofLp 1 + r i * Real.sin (a i))
    (hnn : ∀ i, i < m → 0 ≤ a i - a (i + 1))
    (hle : ∀ i, i < m → a i - a (i + 1) ≤ Real.pi)
    (hsum : ∑ i ∈ Finset.range m, (a i - a (i + 1)) = 2 * Real.pi) :
    ∑ i ∈ Finset.range m, EuclideanGeometry.angle (p i) v (p (i + 1)) = 2 * Real.pi := by
  rw [← hsum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  have hpol := polar_angle_eq_arccos_cos v (p i) (p (i + 1)) (a i) (a (i + 1))
    (r i) (r (i + 1)) (hr i) (hr (i + 1)) (hp0 i) (hp1 i) (hp0 (i + 1)) (hp1 (i + 1))
  rw [hpol]
  exact Real.arccos_cos (hnn i hi') (hle i hi')

theorem o06_angle_sum_of_polar_fan_desc (h : ℕ) (hh : 3 ≤ h) (v : ℝ^ 2) (p : ℕ → ℝ^ 2)
    (a r : ℕ → ℝ)
    (hper : ∀ i, p (i + h) = p i)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v.ofLp 1 + r i * Real.sin (a i))
    (hnn : ∀ i, i < h → 0 ≤ a i - a (i + 1))
    (hle : ∀ i, i < h → a i - a (i + 1) ≤ Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a i - a (i + 1)) = 2 * Real.pi)
    (hinside : ∀ i, InsideAngleAt v p i) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi :=
  o06_angle_sum_of_interior_point h hh v p hper
    (ne_of_pos_radius v p a r hr hp0 hp1)
    (hcentral_of_polar_desc h v p a r hr hp0 hp1 hnn hle hgap)
    hinside

/-! ## THE SPLICE -- the interior-angle sum of a hull-vertex listing, from polar data alone.

Nothing is assumed here beyond the polar description of the listing: not the angle split,
not the cone containment, not the angle sum.  The only geometric input is that each listed
point is an EXTREME point of the convex set and that the centre lies in it. -/

theorem e1084_hull_angle_sum
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (h : ℕ) (hh : 3 ≤ h)
    (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ A) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hext : ∀ i, p i ∈ A.extremePoints ℝ)
    (hper : ∀ i, p (i + h) = p i)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a i - a (i + 1)) = 2 * Real.pi) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi :=
  o06_angle_sum_of_polar_fan_desc h hh v₀ p a r hper hr hp0 hp1
    (fun i _ => le_of_lt (hpos i)) (fun i _ => le_of_lt (hlt i)) hgap
    (h3_hull_inside A hA v₀ hv₀ p a r hext hr hp0 hp1 hpos hlt)

/-- The same, with `A` the convex hull of the point set `S` the campaign actually carries. -/
theorem e1084_hull_angle_sum_finset
    (S : Finset (ℝ^ 2)) (h : ℕ) (hh : 3 ≤ h)
    (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ convexHull ℝ (S : Set (ℝ^ 2))) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hext : ∀ i, p i ∈ (convexHull ℝ (S : Set (ℝ^ 2))).extremePoints ℝ)
    (hper : ∀ i, p (i + h) = p i)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a i - a (i + 1)) = 2 * Real.pi) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi :=
  e1084_hull_angle_sum (convexHull ℝ (S : Set (ℝ^ 2))) (convex_convexHull ℝ _) h hh
    v₀ hv₀ p a r hext hper hr hp0 hp1 hpos hlt hgap

/-! ## THE MODEL -- the hypotheses of S1, H3 and the splice are NOT vacuous.

Campaign law, recorded in `O06_PolarFan_Handoff_Desc.lean` after the ascending/descending
orientation defect survived a whole rung: *a socket offered UNMODELLED is how a false
statement survives*. So the repaired S1 is modelled before it is used.

The model is the CLOCKWISE unit square, listed about its centre, taken as extreme points of
the closed unit BALL -- which sidesteps Mathlib's missing extremePoints/frontier bridge
entirely, since a point of norm `1` is extreme in the ball by strict convexity. The
conclusion reproduced, `Σ interior angles = 2π` on the square, was independently sealed by
the other route (`o06_polar_fan_desc_model`), so this is also a cross-check of the new path.
-/

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

noncomputable def W4 : ℕ → ℝ^ 2
  | 0 => pt2 1 0
  | 1 => pt2 0 (-1)
  | 2 => pt2 (-1) 0
  | _ => pt2 0 1

noncomputable def ww (i : ℕ) : ℝ^ 2 := W4 (i % 4)

theorem ww_per (i : ℕ) : ww (i + 4) = ww i := by
  simp only [ww]; congr 1; omega

/-- A quarter turn CLOCKWISE per step: the descending argument function of `ww`. -/
noncomputable def aa (i : ℕ) : ℝ := -(Real.pi / 2) * (i : ℝ)

theorem aa_cos (i : ℕ) : Real.cos (aa i) = Real.cos (aa (i % 4)) := by
  have hsplit : (i : ℝ) = ((i % 4 : ℕ) : ℝ) + 4 * ((i / 4 : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.mod_add_div i 4).symm
  simp only [aa]
  rw [hsplit, show -(Real.pi/2) * (((i % 4 : ℕ):ℝ) + 4 * ((i/4 : ℕ):ℝ))
      = -(Real.pi/2) * ((i % 4 : ℕ):ℝ) - ((i/4 : ℕ):ℝ) * (2*Real.pi) by ring]
  exact Real.cos_periodic.sub_nat_mul_eq (i/4)

theorem aa_sin (i : ℕ) : Real.sin (aa i) = Real.sin (aa (i % 4)) := by
  have hsplit : (i : ℝ) = ((i % 4 : ℕ) : ℝ) + 4 * ((i / 4 : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.mod_add_div i 4).symm
  simp only [aa]
  rw [hsplit, show -(Real.pi/2) * (((i % 4 : ℕ):ℝ) + 4 * ((i/4 : ℕ):ℝ))
      = -(Real.pi/2) * ((i % 4 : ℕ):ℝ) - ((i/4 : ℕ):ℝ) * (2*Real.pi) by ring]
  exact Real.sin_periodic.sub_nat_mul_eq (i/4)

theorem c32 : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show (3 * Real.pi / 2) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_two, neg_zero]
theorem s32 : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show (3 * Real.pi / 2) = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_two]

theorem ww_polar0 (i : ℕ) : (ww i).ofLp 0 = (pt2 0 0).ofLp 0 + 1 * Real.cos (aa i) := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rw [aa_cos i]
  rcases h with h | h | h | h <;>
    simp [ww, h, W4, pt2, aa, Real.cos_pi_div_two, Real.cos_pi, c32, Real.cos_neg,
          show -(Real.pi/2) * (3:ℝ) = -(3 * Real.pi / 2) by ring,
          show -(Real.pi/2) * (2:ℝ) = -Real.pi by ring,
          show -(Real.pi/2) * (1:ℝ) = -(Real.pi/2) by ring]

theorem ww_polar1 (i : ℕ) : (ww i).ofLp 1 = (pt2 0 0).ofLp 1 + 1 * Real.sin (aa i) := by
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rw [aa_sin i]
  rcases h with h | h | h | h <;>
    simp [ww, h, W4, pt2, aa, Real.sin_pi_div_two, Real.sin_pi, s32, Real.sin_neg,
          show -(Real.pi/2) * (3:ℝ) = -(3 * Real.pi / 2) by ring,
          show -(Real.pi/2) * (2:ℝ) = -Real.pi by ring,
          show -(Real.pi/2) * (1:ℝ) = -(Real.pi/2) by ring]

theorem aa_gap (i : ℕ) : aa i - aa (i + 1) = Real.pi / 2 := by
  simp only [aa]; push_cast; ring

theorem zero0 : (0 : ℝ^ 2).ofLp 0 = 0 := rfl
theorem zero1 : (0 : ℝ^ 2).ofLp 1 = 0 := rfl

theorem pt2_zero : pt2 0 0 = (0 : ℝ^ 2) := by
  refine pt_ext _ _ ?_ ?_ <;> simp [pt2, zero0, zero1]

theorem ww_pol0 (i : ℕ) :
    (ww i).ofLp 0 = (0 : ℝ^ 2).ofLp 0 + 1 * Real.cos (aa i) := by
  have h := ww_polar0 i; rwa [pt2_zero] at h

theorem ww_pol1 (i : ℕ) :
    (ww i).ofLp 1 = (0 : ℝ^ 2).ofLp 1 + 1 * Real.sin (aa i) := by
  have h := ww_polar1 i; rwa [pt2_zero] at h

theorem norm_of_polar (x : ℝ^ 2) (t : ℝ)
    (h0 : x.ofLp 0 = Real.cos t) (h1 : x.ofLp 1 = Real.sin t) : ‖x‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, h0, h1]
  rw [show Real.cos t ^ 2 + Real.sin t ^ 2 = 1 by
    have := Real.sin_sq_add_cos_sq t; linarith]
  exact Real.sqrt_one

/-- A point of norm `1` is an EXTREME point of the closed unit ball -- strict convexity,
no hull and no frontier. -/
theorem sphere_extreme (x : ℝ^ 2) (hx : ‖x‖ = 1) :
    x ∈ (Metric.closedBall (0 : ℝ^ 2) 1).extremePoints ℝ := by
  rw [mem_extremePoints]
  have hxm : x ∈ Metric.closedBall (0 : ℝ^ 2) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, hx]
  refine ⟨hxm, ?_⟩
  rintro y hy z hz ⟨s, t, hs, ht, hst, hxyz⟩
  have hny : ‖y‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have hnz : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  by_cases hyz : y = z
  · rw [hyz] at hxyz
    have hy2 : z = x := by rw [← hxyz, ← add_smul, hst, one_smul]
    exact ⟨hyz.trans hy2, hy2⟩
  · exfalso
    have hlt := norm_combo_lt_of_ne hny hnz hyz hs ht hst
    rw [hxyz, hx] at hlt
    linarith

theorem ww_norm (i : ℕ) : ‖ww i‖ = 1 := by
  refine norm_of_polar (ww i) (aa i) ?_ ?_
  · have h := ww_pol0 i; rw [zero0] at h; linarith
  · have h := ww_pol1 i; rw [zero1] at h; linarith

theorem ww_ext (i : ℕ) : ww i ∈ (Metric.closedBall (0 : ℝ^ 2) 1).extremePoints ℝ :=
  sphere_extreme _ (ww_norm i)

/-- ⛔ THE MODEL, END TO END.  Every hypothesis of `e1084_hull_angle_sum` holds
simultaneously on the clockwise unit square about its centre, and the theorem returns the
square's interior-angle sum `2π`. -/
theorem e1084_hull_angle_sum_square :
    ∑ i ∈ Finset.range 4,
        EuclideanGeometry.angle (ww i) (ww (i + 1)) (ww (i + 2)) = ((4 : ℝ) - 2) * Real.pi := by
  have hpi := Real.pi_pos
  have hgap : ∑ i ∈ Finset.range 4, (aa i - aa (i + 1)) = 2 * Real.pi := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
    rw [aa_gap 0, aa_gap 1, aa_gap 2, aa_gap 3]
    ring
  simpa using
    e1084_hull_angle_sum (Metric.closedBall (0 : ℝ^ 2) 1) (convex_closedBall _ _)
      4 (by norm_num) 0 (by simp) ww aa (fun _ => 1)
      ww_ext ww_per (fun _ => by norm_num) ww_pol0 ww_pol1
      (fun i => by rw [aa_gap i]; linarith)
      (fun i => by rw [aa_gap i]; linarith)
      hgap

#print axioms s1_consecutive_signs
#print axioms h3_hull_inside
#print axioms e1084_hull_angle_sum
#print axioms e1084_hull_angle_sum_finset
#print axioms e1084_hull_angle_sum_square
