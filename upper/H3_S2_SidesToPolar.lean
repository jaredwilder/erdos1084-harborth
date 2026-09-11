import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open Complex

/-! # erdos:1084 upper -- S2, THE TRIGONOMETRIC CONVERSION, PROVED.

Obligation S2 of the H3 decomposition: two STRICT same-side conditions plus the orientation
put `v` inside the open cone at the vertex and order the three polar arguments about it with
every arc at most `π`.  No hull, no convexity -- plane trigonometry only.

The orientation hypothesis is not decoration: `InsideAngleAt` requires the turn at the
vertex to be non-negative, so it selects the CLOCKWISE listing, and without `0 < cross Y X Z`
the statement is false (`O06_S2_Refutation.lean` refutes the version that lacked it).

METHOD.  Move to `ℂ`, where the argument function and its additivity already exist.  Set
`u = X - Y`, `t = v - Y`, `w = Z - Y`.  The three cross products are the imaginary parts of
`t/u`, `w/t` and `w/u`, so the hypotheses say exactly that those three quotients lie in the
upper half plane.  Take `α = arg u`, `β = α + arg (t/u)`, `γ = β + arg (w/t)`; each step adds
an argument in `(0, π)`, and the total is an argument of `w/u`, whose positive imaginary part
forbids it from exceeding `π`.
-/

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
  -- the three cross products as imaginary parts
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
  -- nonvanishing
  have hu0 : u ≠ 0 := by
    intro hz; rw [hz] at hor; simp at hor
  have hw0 : w ≠ 0 := by
    intro hz; rw [hz] at hor; simp at hor
  have ht0 : t ≠ 0 := by
    intro hz; rw [hz] at hut; simp at hut
  have hnu : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu0
  have hnt : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
  -- the three quotients lie in the upper half plane
  have him1 : 0 < (t / u).im := by
    rw [im_div]; exact div_pos hut hnu
  have him2 : 0 < (w / t).im := by
    rw [im_div]; exact div_pos htw hnt
  have him3 : 0 < (w / u).im := by
    rw [im_div]; exact div_pos hor hnu
  obtain ⟨hp1, hq1⟩ := arg_mem_Ioo him1
  obtain ⟨hp2, hq2⟩ := arg_mem_Ioo him2
  -- the three arguments
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
  -- the total arc is at most pi, because it is an argument of a point in the upper half plane
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

  -- assemble
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

#print axioms s2_sides_to_polar
