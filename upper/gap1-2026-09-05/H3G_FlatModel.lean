import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open Complex
open scoped Classical

/-! # erdos:1084 upper -- GAP 1 CLOSED: the angle sum over FRONTIER points.

`H3_Assembled.lean` sealed `e1084_hull_angle_sum` for a listing of EXTREME points.
`H05_Assembly.lean`'s `FanInterface` indexes `hullPts S = {v ∈ S | v ∈ frontier (convexHull S)}`
and demands surjectivity onto it.  The two sets differ exactly at a point of `S` lying in the
relative interior of a hull edge, and Mathlib has no bridge (its own TODO).  This file closes
both halves of that gap:

* **(1a)** `extremePoint_mem_frontier` / `vertexPts_subset_hullPts` -- the cheap direction,
  proved WITHOUT a separating functional: an extreme point cannot be interior, because an
  interior point is the midpoint of two distinct points of the set.
  `convexHull_subset_hullPts` then upgrades it to the covering the ceiling argument needs.

* **(1b)** THE DEGENERATE BRANCH.  `s1_consecutive_signs` proved `0 < cross (p (i+1)) (p i)
  (p (i+2))`, which is FALSE at a collinear listed triple, so it can never index `hullPts`.
  Here the whole chain is re-proved with `0 ≤ cross ...`, and the extremality hypothesis is
  replaced by the two facts `hullPts` actually gives: the centre is INTERIOR, and every listed
  point is NOT.  A strictly-right turn would place the middle point on an open segment from an
  interior point to a point of the set, hence in the interior -- forbidden.  A straight turn is
  now admitted and carries interior angle exactly `π`.

⛔ NOTHING here assumes the listing is extreme.  `e1084_frontier_angle_sum` consumes exactly
`hullPts` membership.
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

def IsArg (x : ℝ) (z : ℂ) : Prop :=
  Real.cos x = z.re / ‖z‖ ∧ Real.sin x = z.im / ‖z‖

noncomputable def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

noncomputable def vertexPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ (convexHull ℝ (S : Set (ℝ^ 2))).extremePoints ℝ}

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

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

theorem pt2_0 (x y : ℝ) : (pt2 x y).ofLp 0 = x := rfl
theorem pt2_1 (x y : ℝ) : (pt2 x y).ofLp 1 = y := rfl

theorem norm_coord (x : ℝ^ 2) : ‖x‖ = Real.sqrt (x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem norm_pt2 (x y : ℝ) : ‖pt2 x y‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [norm_coord, pt2_0, pt2_1]

/-! ## (1a) AN EXTREME POINT IS NOT INTERIOR -- hence it is on the frontier.

Mathlib records the missing `extremePoints` ↔ `frontier` bridge as its own TODO
(`Analysis/Convex/Extreme.lean`).  The cheap direction needs no supporting hyperplane at all:
an interior point has a whole ball around it, so it is the midpoint of two distinct points of
the set, which extremality forbids. -/

theorem extremePoints_not_interior (A : Set (ℝ^ 2)) (x : ℝ^ 2)
    (hx : x ∈ A.extremePoints ℝ) : x ∉ interior A := by
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hint
  set d : ℝ^ 2 := pt2 (ε / 2) 0 with hd
  have hnd : ‖d‖ = ε / 2 := by
    rw [hd, norm_pt2, show (ε / 2) ^ 2 + (0 : ℝ) ^ 2 = (ε / 2) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
  have hd1 : dist (x + d) x = ε / 2 := by rw [dist_eq_norm, add_sub_cancel_left, hnd]
  have hd2 : dist (x - d) x = ε / 2 := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, hnd]
  have hyA : x + d ∈ A :=
    interior_subset (hball (by simp only [Metric.mem_ball, hd1]; linarith))
  have hzA : x - d ∈ A :=
    interior_subset (hball (by simp only [Metric.mem_ball, hd2]; linarith))
  have hseg : x ∈ openSegment ℝ (x + d) (x - d) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  obtain ⟨h1, -⟩ := (mem_extremePoints.mp hx).2 (x + d) hyA (x - d) hzA hseg
  have hd0 : d = 0 := by
    have := h1
    simpa using this
  rw [hd0, norm_zero] at hnd
  linarith

theorem extremePoint_mem_frontier (A : Set (ℝ^ 2)) (x : ℝ^ 2)
    (hx : x ∈ A.extremePoints ℝ) : x ∈ frontier A :=
  ⟨subset_closure (extremePoints_subset hx), extremePoints_not_interior A x hx⟩

theorem mem_hullPts_iff {S : Finset (ℝ^ 2)} {v : ℝ^ 2} :
    v ∈ hullPts S ↔ v ∈ S ∧ v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2))) := by
  simp only [hullPts, Finset.mem_filter]

theorem mem_vertexPts_iff {S : Finset (ℝ^ 2)} {v : ℝ^ 2} :
    v ∈ vertexPts S ↔ v ∈ S ∧ v ∈ (convexHull ℝ (S : Set (ℝ^ 2))).extremePoints ℝ := by
  simp only [vertexPts, Finset.mem_filter]

/-- ⛔ GAP 1a, in the campaign's own vocabulary: the vertex index of `H3X` is a sub-index of
the frontier index of `H05`. -/
theorem vertexPts_subset_hullPts (S : Finset (ℝ^ 2)) : vertexPts S ⊆ hullPts S := by
  intro v hv
  rw [mem_vertexPts_iff] at hv
  rw [mem_hullPts_iff]
  exact ⟨hv.1, extremePoint_mem_frontier _ _ hv.2⟩

/-- The covering the gap ceiling needs: the hull of `S` is the hull of its FRONTIER points.
Krein-Milman closes it, because the hull of a finite set is compact and the hull of the
(finite) extreme set is closed. -/
theorem convexHull_subset_hullPts (S : Finset (ℝ^ 2)) :
    convexHull ℝ (S : Set (ℝ^ 2)) ⊆ convexHull ℝ (hullPts S : Set (ℝ^ 2)) := by
  have hfin : (S : Set (ℝ^ 2)).Finite := S.finite_toSet
  have hKM := closure_convexHull_extremePoints (hfin.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (S : Set (ℝ^ 2)))
  have hsub : (convexHull ℝ (S : Set (ℝ^ 2))).extremePoints ℝ ⊆ (hullPts S : Set (ℝ^ 2)) := by
    intro x hx
    have hxS : x ∈ (S : Set (ℝ^ 2)) := extremePoints_convexHull_subset hx
    have hxf : x ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2))) :=
      extremePoint_mem_frontier _ _ hx
    exact Finset.mem_coe.mpr (mem_hullPts_iff.mpr ⟨Finset.mem_coe.mp hxS, hxf⟩)
  calc convexHull ℝ (S : Set (ℝ^ 2))
      = closure (convexHull ℝ ((convexHull ℝ (S : Set (ℝ^ 2))).extremePoints ℝ)) := hKM.symm
    _ ⊆ closure (convexHull ℝ (hullPts S : Set (ℝ^ 2))) :=
        closure_mono (convexHull_mono hsub)
    _ = convexHull ℝ (hullPts S : Set (ℝ^ 2)) :=
        IsClosed.closure_eq ((hullPts S).finite_toSet.isClosed_convexHull ℝ)

/-! ## (1b) S2, GENERALIZED TO A NON-STRICT TURN.

`s2_sides_to_polar` demanded `0 < cross Y X Z` and two cross-product PRODUCTS.  The products
were only ever a way to transport two signs; state them directly, and the orientation
relaxes to `0 ≤`.  At equality the three points are collinear and `γ - α` is exactly `π` --
the flat vertex, whose interior angle is `π`. -/

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

/-- ⛔ S2≥, PROVED.  The centre `v` lies inside the angle at `Y` as soon as it is strictly
left of the ray to `X`, strictly left of the ray to `Z` (in that cyclic order), and the turn
`X → Y → Z` is not strictly right.  `0 ≤ cross Y X Z` -- the flat vertex is ADMITTED. -/
theorem s2_sides_to_polar_ge (v X Y Z : ℝ^ 2)
    (hut : 0 < cross Y X v)
    (htw : 0 < cross Y v Z)
    (hor : 0 ≤ cross Y X Z)
    (p : ℕ → ℝ^ 2) (i : ℕ) (hpi : p i = X) (hpi1 : p (i + 1) = Y) (hpi2 : p (i + 2) = Z) :
    InsideAngleAt v p i := by
  set u : ℂ := toC X - toC Y with hu
  set t : ℂ := toC v - toC Y with ht
  set w : ℂ := toC Z - toC Y with hw
  have cXZ : cross Y X Z = u.re * w.im - u.im * w.re := by
    simp only [cross, hu, hw, toC_sub_re, toC_sub_im]
  have cXv : cross Y X v = u.re * t.im - u.im * t.re := by
    simp only [cross, hu, ht, toC_sub_re, toC_sub_im]
  have cvZ : cross Y v Z = t.re * w.im - t.im * w.re := by
    simp only [cross, ht, hw, toC_sub_re, toC_sub_im]
  rw [cXZ] at hor
  rw [cXv] at hut
  rw [cvZ] at htw
  have hu0 : u ≠ 0 := by intro hz; rw [hz] at hut; simp at hut
  have ht0 : t ≠ 0 := by intro hz; rw [hz] at hut; simp at hut
  have hw0 : w ≠ 0 := by intro hz; rw [hz] at htw; simp at htw
  have hnu : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu0
  have hnt : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
  have him1 : 0 < (t / u).im := by rw [im_div]; exact div_pos hut hnu
  have him2 : 0 < (w / t).im := by rw [im_div]; exact div_pos htw hnt
  have him3 : 0 ≤ (w / u).im := by
    rw [im_div]; exact div_nonneg hor (le_of_lt hnu)
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
    have hmul : (t / u) * (w / t) = w / u := by field_simp
    rw [hmul] at hArg
    have hsinnn : 0 ≤ Real.sin ((t / u).arg + (w / t).arg) := by
      rw [hArg.2]
      exact div_nonneg him3 (norm_nonneg _)
    have hsum : (t / u).arg + (w / t).arg = γ - α := by simp only [hγ, hβ]; ring
    rw [hsum] at hsinnn
    have hlt2pi : γ - α < 2 * Real.pi := by simp only [hγ, hβ]; linarith
    have h0 : 0 < γ - α - Real.pi := by linarith
    have h1' : γ - α - Real.pi < Real.pi := by linarith
    have hpos := Real.sin_pos_of_pos_of_lt_pi h0 h1'
    have heq : Real.sin (γ - α) = -Real.sin (γ - α - Real.pi) := by
      rw [show γ - α = (γ - α - Real.pi) + Real.pi by ring, Real.sin_add_pi]
      ring_nf
    rw [heq] at hsinnn
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

/-! ## (1b) S1, WITH EXTREMALITY REPLACED BY "NOT INTERIOR". -/

/-- CRAMER, strict form.  A STRICTLY right turn makes the middle direction a convex
combination of the outer two with total weight STRICTLY below one -- i.e. the middle point is
strictly between the centre and the far chord. -/
theorem cross_core_strict (u0 u1 m0 m1 w0 w1 : ℝ)
    (hum : u0 * m1 - u1 * m0 < 0)
    (hmw : m0 * w1 - m1 * w0 < 0)
    (hneg : u0 * w1 - u1 * w0 < 0)
    (hcon : u0 * w1 - u1 * w0 - (u0 * m1 - u1 * m0) - (m0 * w1 - m1 * w0) < 0) :
    ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ lam + mu < 1 ∧
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
  have hkey : u0 * w1 - u1 * w0 - (u0 * m1 - u1 * m0) - (m0 * w1 - m1 * w0)
      = (u0 * w1 - u1 * w0) * (1 - mu - lam) := by
    rw [huxm, hmxw]; ring
  have hsum : lam + mu < 1 := by
    by_contra hx
    push_neg at hx
    have hprod : (u0 * w1 - u1 * w0) * (1 - mu - lam) < 0 := by rw [← hkey]; exact hcon
    nlinarith [hprod, hneg, hx]
  exact ⟨lam, mu, hlam, hmu, hsum, hc0, hc1⟩

/-- A point strictly between an INTERIOR point and a point of the set is interior. -/
theorem interior_combo_mem
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (v₀ X Z Y : ℝ^ 2)
    (hv : v₀ ∈ interior A) (hX : X ∈ A) (hZ : Z ∈ A)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hsum : lam + mu < 1)
    (hrep : Y = (1 - (lam + mu)) • v₀ + (lam • X + mu • Z)) : Y ∈ interior A := by
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
  exact hA.openSegment_interior_self_subset_interior hv hcA
    ⟨1 - (lam + mu), lam + mu, by linarith, hs0, by ring, hsc⟩

/-- ⛔ S1≥, PROVED.  A listing described in polar coordinates about an INTERIOR point `v₀`,
with strictly descending arguments and every consecutive gap strictly below `π`, and with
every listed point OUTSIDE the interior (i.e. on the frontier), has: the centre strictly left
of both rays at every vertex, and a turn that is never strictly right. -/
theorem s1_frontier_signs
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ interior A)
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hmem : ∀ i, p i ∈ A)
    (hfr : ∀ i, p i ∉ interior A)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi)
    (i : ℕ) :
    0 < cross (p (i + 1)) (p i) v₀ ∧
    0 < cross (p (i + 1)) v₀ (p (i + 2)) ∧
    0 ≤ cross (p (i + 1)) (p i) (p (i + 2)) := by
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
  have E2 : cross (p (i + 1)) v₀ (p (i + 2))
      = -(r (i + 1) * Real.cos (a (i + 1)) * (r (i + 2) * Real.sin (a (i + 2)))
          - r (i + 1) * Real.sin (a (i + 1)) * (r (i + 2) * Real.cos (a (i + 2)))) := by
    simp only [cross, hp0, hp1]; ring
  have E3 : cross (p (i + 1)) (p i) (p (i + 2))
      = r i * Real.cos (a i) * (r (i + 2) * Real.sin (a (i + 2)))
          - r i * Real.sin (a i) * (r (i + 2) * Real.cos (a (i + 2)))
        - (r i * Real.cos (a i) * (r (i + 1) * Real.sin (a (i + 1)))
          - r i * Real.sin (a i) * (r (i + 1) * Real.cos (a (i + 1))))
        - (r (i + 1) * Real.cos (a (i + 1)) * (r (i + 2) * Real.sin (a (i + 2)))
          - r (i + 1) * Real.sin (a (i + 1)) * (r (i + 2) * Real.cos (a (i + 2)))) := by
    simp only [cross, hp0, hp1]; ring
  refine ⟨by rw [E1]; linarith, by rw [E2]; linarith, ?_⟩
  by_contra hcon
  push_neg at hcon
  rw [E3] at hcon
  have hD : r i * Real.cos (a i) * (r (i + 2) * Real.sin (a (i + 2)))
      - r i * Real.sin (a i) * (r (i + 2) * Real.cos (a (i + 2))) < 0 := by linarith
  obtain ⟨lam, mu, hlam, hmu, hsum, hc0, hc1⟩ :=
    cross_core_strict (r i * Real.cos (a i)) (r i * Real.sin (a i))
      (r (i + 1) * Real.cos (a (i + 1))) (r (i + 1) * Real.sin (a (i + 1)))
      (r (i + 2) * Real.cos (a (i + 2))) (r (i + 2) * Real.sin (a (i + 2)))
      hum hmw hD hcon
  have hrep : p (i + 1)
      = (1 - (lam + mu)) • v₀ + (lam • p i + mu • p (i + 2)) := by
    refine pt_ext _ _ ?_ ?_
    · simp only [ad0, sm0, hp0]
      linear_combination hc0
    · simp only [ad1, sm1, hp1]
      linear_combination hc1
  exact hfr (i + 1)
    (interior_combo_mem A hA v₀ (p i) (p (i + 2)) (p (i + 1)) hv₀ (hmem i) (hmem (i + 2))
      lam mu hlam hmu hsum hrep)

/-- ⛔ H3≥, PROVED.  The frontier listing puts `v₀` inside the angle at every vertex,
degenerate (flat) vertices included. -/
theorem h3_frontier_inside
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ interior A)
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hmem : ∀ i, p i ∈ A)
    (hfr : ∀ i, p i ∉ interior A)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi) :
    ∀ i, InsideAngleAt v₀ p i := by
  intro i
  obtain ⟨h1, h2, h3⟩ :=
    s1_frontier_signs A hA v₀ hv₀ p a r hmem hfr hr hp0 hp1 hpos hlt i
  exact s2_sides_to_polar_ge v₀ (p i) (p (i + 1)) (p (i + 2)) h1 h2 h3 p i rfl rfl rfl

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
  rw [e1, e2, e3, c1, c2, c3, Real.arccos_cos hab hab', Real.arccos_cos hbc hbc',
      Real.arccos_cos (by linarith) hac']
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

/-! ## ⛔ THE SPLICE, FRONTIER-INDEXED.  This is the statement `H05`'s `FanInterface` needs. -/

theorem e1084_frontier_angle_sum
    (A : Set (ℝ^ 2)) (hA : Convex ℝ A) (h : ℕ) (hh : 3 ≤ h)
    (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ interior A) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hmem : ∀ i, p i ∈ A)
    (hfr : ∀ i, p i ∉ interior A)
    (hper : ∀ i, p (i + h) = p i)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a i - a (i + 1)) = 2 * Real.pi) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi :=
  o06_fan_angle_sum h hh v₀ p hper (ne_of_pos_radius v₀ p a r hr hp0 hp1)
    (hcentral_of_polar_desc h v₀ p a r hr hp0 hp1
      (fun i _ => le_of_lt (hpos i)) (fun i _ => le_of_lt (hlt i)) hgap)
    (fun i => hadd_of_inside v₀ p i
      (h3_frontier_inside A hA v₀ hv₀ p a r hmem hfr hr hp0 hp1 hpos hlt i))

/-- The same, indexed by `hullPts S` -- verbatim the index `H05_Assembly.FanInterface` uses. -/
theorem e1084_hullPts_angle_sum
    (S : Finset (ℝ^ 2)) (h : ℕ) (hh : 3 ≤ h)
    (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))))
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hmem : ∀ i, p i ∈ hullPts S)
    (hper : ∀ i, p (i + h) = p i)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hlt : ∀ i, a i - a (i + 1) < Real.pi)
    (hgap : ∑ i ∈ Finset.range h, (a i - a (i + 1)) = 2 * Real.pi) :
    ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
      = ((h : ℝ) - 2) * Real.pi := by
  refine e1084_frontier_angle_sum (convexHull ℝ (S : Set (ℝ^ 2))) (convex_convexHull ℝ _)
    h hh v₀ hv₀ p a r ?_ ?_ hper hr hp0 hp1 hpos hlt hgap
  · intro i
    exact subset_convexHull ℝ (S : Set (ℝ^ 2)) (Finset.mem_coe.mpr (mem_hullPts_iff.mp (hmem i)).1)
  · intro i
    exact (mem_hullPts_iff.mp (hmem i)).2.2


/-! ## ⛔ THE DEGENERATE MODEL -- the flat vertex is REAL, and this file's statement admits it.

Campaign law (`O06_PolarFan_Handoff_Desc.lean`): *a socket offered UNMODELLED is how a false
statement survives*.  `e1084_frontier_angle_sum` claims something `e1084_hull_angle_sum`
cannot: a listing containing a NON-EXTREME frontier point.  So a listing of that exact kind is
built and run through it.

THE CONFIGURATION.  `A` = the horizontal strip `|y| ≤ 1` (convex, with an easy interior), the
centre is the origin, and the listing is the four corners of the square PLUS the midpoint
`(0,1)` of its top edge:

```
   (-1,1) ---- (0,1) ---- (1,1)      <- three COLLINEAR listed points
      |                      |
      |          0           |       <- v0, interior
      |                      |
   (-1,-1) ------------ (1,-1)
```

listed clockwise from `(0,1)` at polar angles `π/2, π/4, -π/4, -3π/4, -5π/4`, i.e. gaps
`π/4, π/2, π/2, π/2, π/4` summing to `2π`.  `h = 5`, and the interior angles sum to `3π`.

⛔ `flat_cross_zero` proves `cross (qq 5) (qq 4) (qq 6) = 0`: at the flat vertex the STRICT
cross product that `s1_consecutive_signs` concludes is FALSE, so this configuration is
provably outside the sealed extreme-point route.  `flat_angle_pi` proves the flat vertex
carries interior angle exactly `π`.  The degenerate branch is not a formality. -/

noncomputable def Strip : Set (ℝ^ 2) := {x : ℝ^ 2 | x.ofLp 1 ≤ 1 ∧ (-1 : ℝ) ≤ x.ofLp 1}

theorem strip_convex : Convex ℝ Strip := by
  intro x hx y hy t1 t2 ht1 ht2 ht
  simp only [Strip, Set.mem_setOf_eq] at hx hy ⊢
  have e1 : ((t1 • x + t2 • y : ℝ^ 2)).ofLp 1 = t1 * x.ofLp 1 + t2 * y.ofLp 1 := rfl
  rw [e1]
  constructor
  · nlinarith [hx.1, hy.1]
  · nlinarith [hx.2, hy.2]

theorem abs_coord1_le_norm (x : ℝ^ 2) : |x.ofLp 1| ≤ ‖x‖ := by
  rw [norm_coord, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x.ofLp 0)])

theorem strip_zero_interior : (0 : ℝ^ 2) ∈ interior Strip := by
  rw [mem_interior]
  refine ⟨Metric.ball (0 : ℝ^ 2) 1, ?_, Metric.isOpen_ball, by simp [Metric.mem_ball]⟩
  intro x hx
  have hn : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have habs := abs_coord1_le_norm x
  have h1 := abs_le.mp (le_of_lt (lt_of_le_of_lt habs hn))
  exact ⟨h1.2, h1.1⟩

theorem strip_interior_strict (x : ℝ^ 2) (hx : x ∈ interior Strip) :
    x.ofLp 1 < 1 ∧ -1 < x.ofLp 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hnorm : ∀ t : ℝ, ‖pt2 0 t‖ = |t| := by
    intro t
    rw [norm_pt2, show (0:ℝ) ^ 2 + t ^ 2 = t ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hstep : ∀ t : ℝ, |t| < ε → x + pt2 0 t ∈ Strip := by
    intro t ht
    refine interior_subset (hball ?_)
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
    exact ht
  have hcoord : ∀ t : ℝ, (x + pt2 0 t).ofLp 1 = x.ofLp 1 + t := by
    intro t
    rw [ad1, pt2_1]
  constructor
  · have h := (hstep (ε / 2) (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ε / 2)]; linarith)).1
    rw [hcoord] at h
    linarith
  · have h := (hstep (-(ε / 2)) (by rw [abs_of_nonpos (by linarith : -(ε/2) ≤ (0:ℝ))]; linarith)).2
    rw [hcoord] at h
    linarith

/-! ### The listing. -/

noncomputable def Q5 : ℕ → ℝ^ 2
  | 0 => pt2 0 1
  | 1 => pt2 1 1
  | 2 => pt2 1 (-1)
  | 3 => pt2 (-1) (-1)
  | _ => pt2 (-1) 1

noncomputable def qq (i : ℕ) : ℝ^ 2 := Q5 (i % 5)

noncomputable def rr5 (i : ℕ) : ℝ := if i % 5 = 0 then 1 else Real.sqrt 2

noncomputable def GP : ℕ → ℝ
  | 0 => Real.pi / 4
  | 1 => Real.pi / 2
  | 2 => Real.pi / 2
  | 3 => Real.pi / 2
  | _ => Real.pi / 4

noncomputable def gap5 (i : ℕ) : ℝ := GP (i % 5)

noncomputable def a5 : ℕ → ℝ
  | 0 => Real.pi / 2
  | (n + 1) => a5 n - gap5 n

theorem a5_zero : a5 0 = Real.pi / 2 := rfl
theorem a5_succ (n : ℕ) : a5 (n + 1) = a5 n - gap5 n := rfl

theorem gap5_0 : gap5 0 = Real.pi / 4 := rfl
theorem gap5_1 : gap5 1 = Real.pi / 2 := rfl
theorem gap5_2 : gap5 2 = Real.pi / 2 := rfl
theorem gap5_3 : gap5 3 = Real.pi / 2 := rfl
theorem gap5_4 : gap5 4 = Real.pi / 4 := rfl

theorem gap5_pos (i : ℕ) : 0 < gap5 i := by
  have hpi := Real.pi_pos
  have h : i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
  rcases h with h | h | h | h | h <;> simp only [gap5, h, GP] <;> linarith

theorem gap5_lt_pi (i : ℕ) : gap5 i < Real.pi := by
  have hpi := Real.pi_pos
  have h : i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
  rcases h with h | h | h | h | h <;> simp only [gap5, h, GP] <;> linarith

theorem a5_gap (i : ℕ) : a5 i - a5 (i + 1) = gap5 i := by rw [a5_succ]; ring

theorem qq_per (i : ℕ) : qq (i + 5) = qq i := by
  simp only [qq]; congr 1; omega

theorem rr5_per (i : ℕ) : rr5 (i + 5) = rr5 i := by
  have h : (i + 5) % 5 = i % 5 := by omega
  simp only [rr5, h]

theorem rr5_pos (i : ℕ) : 0 < rr5 i := by
  rw [rr5]
  split
  · norm_num
  · positivity

/-! ### The period of the argument function. -/

theorem a5_period (i : ℕ) : a5 (i + 5) = a5 i - 2 * Real.pi := by
  have e1 : a5 (i + 1) = a5 i - gap5 i := a5_succ i
  have e2 : a5 (i + 2) = a5 (i + 1) - gap5 (i + 1) := a5_succ (i + 1)
  have e3 : a5 (i + 3) = a5 (i + 2) - gap5 (i + 2) := a5_succ (i + 2)
  have e4 : a5 (i + 4) = a5 (i + 3) - gap5 (i + 3) := a5_succ (i + 3)
  have e5 : a5 (i + 5) = a5 (i + 4) - gap5 (i + 4) := a5_succ (i + 4)
  have hsum : gap5 i + gap5 (i + 1) + gap5 (i + 2) + gap5 (i + 3) + gap5 (i + 4)
      = 2 * Real.pi := by
    have h : i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
    rcases h with h | h | h | h | h
    · have r1 : (i + 1) % 5 = 1 := by omega
      have r2 : (i + 2) % 5 = 2 := by omega
      have r3 : (i + 3) % 5 = 3 := by omega
      have r4 : (i + 4) % 5 = 4 := by omega
      simp only [gap5, h, r1, r2, r3, r4, GP]; ring
    · have r1 : (i + 1) % 5 = 2 := by omega
      have r2 : (i + 2) % 5 = 3 := by omega
      have r3 : (i + 3) % 5 = 4 := by omega
      have r4 : (i + 4) % 5 = 0 := by omega
      simp only [gap5, h, r1, r2, r3, r4, GP]; ring
    · have r1 : (i + 1) % 5 = 3 := by omega
      have r2 : (i + 2) % 5 = 4 := by omega
      have r3 : (i + 3) % 5 = 0 := by omega
      have r4 : (i + 4) % 5 = 1 := by omega
      simp only [gap5, h, r1, r2, r3, r4, GP]; ring
    · have r1 : (i + 1) % 5 = 4 := by omega
      have r2 : (i + 2) % 5 = 0 := by omega
      have r3 : (i + 3) % 5 = 1 := by omega
      have r4 : (i + 4) % 5 = 2 := by omega
      simp only [gap5, h, r1, r2, r3, r4, GP]; ring
    · have r1 : (i + 1) % 5 = 0 := by omega
      have r2 : (i + 2) % 5 = 1 := by omega
      have r3 : (i + 3) % 5 = 2 := by omega
      have r4 : (i + 4) % 5 = 3 := by omega
      simp only [gap5, h, r1, r2, r3, r4, GP]; ring
  linarith

theorem a5_shift (n i : ℕ) : a5 (i + n * 5) = a5 i - (n : ℝ) * (2 * Real.pi) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have e : i + (m + 1) * 5 = (i + m * 5) + 5 := by ring
    rw [e, a5_period, ih]
    push_cast
    ring

theorem a5_cos (i : ℕ) : Real.cos (a5 i) = Real.cos (a5 (i % 5)) := by
  have hsplit : a5 i = a5 (i % 5 + (i / 5) * 5) := by rw [Nat.mod_add_div' i 5]
  rw [hsplit, a5_shift]
  exact Real.cos_periodic.sub_nat_mul_eq (i / 5)

theorem a5_sin (i : ℕ) : Real.sin (a5 i) = Real.sin (a5 (i % 5)) := by
  have hsplit : a5 i = a5 (i % 5 + (i / 5) * 5) := by rw [Nat.mod_add_div' i 5]
  rw [hsplit, a5_shift]
  exact Real.sin_periodic.sub_nat_mul_eq (i / 5)

/-! ### The five arguments, and their cosines and sines. -/

theorem a5_v1 : a5 1 = Real.pi / 4 := by rw [a5_succ, a5_zero, gap5_0]; ring

theorem a5_v2 : a5 2 = -(Real.pi / 4) := by
  have h := a5_succ 1
  norm_num at h
  rw [h, a5_v1, gap5_1]; ring

theorem a5_v3 : a5 3 = -(3 * Real.pi / 4) := by
  have h := a5_succ 2
  norm_num at h
  rw [h, a5_v2, gap5_2]; ring

theorem a5_v4 : a5 4 = -(5 * Real.pi / 4) := by
  have h := a5_succ 3
  norm_num at h
  rw [h, a5_v3, gap5_3]; ring

theorem sqrt2_half : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
  rw [show Real.sqrt 2 * (Real.sqrt 2 / 2) = (Real.sqrt 2 * Real.sqrt 2) / 2 by ring,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem cos_3pi4 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show 3 * Real.pi / 4 = Real.pi / 4 + Real.pi / 2 by ring, Real.cos_add_pi_div_two,
      Real.sin_pi_div_four]

theorem sin_3pi4 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [show 3 * Real.pi / 4 = Real.pi / 4 + Real.pi / 2 by ring, Real.sin_add_pi_div_two,
      Real.cos_pi_div_four]

theorem cos_5pi4 : Real.cos (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_four]

theorem sin_5pi4 : Real.sin (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_four]

/-! ### The polar description of the listing about the origin. -/

theorem qq_pol0 (i : ℕ) : (qq i).ofLp 0 = (0 : ℝ^ 2).ofLp 0 + rr5 i * Real.cos (a5 i) := by
  have hz : (0 : ℝ^ 2).ofLp 0 = 0 := rfl
  rw [hz, a5_cos i]
  have h : i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
  rcases h with h | h | h | h | h
  · rw [show qq i = Q5 0 by simp only [qq, h], show rr5 i = 1 by simp [rr5, h], h, a5_zero,
      Real.cos_pi_div_two]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 1 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v1, Real.cos_pi_div_four, sqrt2_half]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 2 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v2, Real.cos_neg, Real.cos_pi_div_four, sqrt2_half]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 3 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v3, Real.cos_neg, cos_3pi4, mul_neg, sqrt2_half]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 4 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v4, Real.cos_neg, cos_5pi4, mul_neg, sqrt2_half]
    norm_num [Q5, pt2]

theorem qq_pol1 (i : ℕ) : (qq i).ofLp 1 = (0 : ℝ^ 2).ofLp 1 + rr5 i * Real.sin (a5 i) := by
  have hz : (0 : ℝ^ 2).ofLp 1 = 0 := rfl
  rw [hz, a5_sin i]
  have h : i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
  rcases h with h | h | h | h | h
  · rw [show qq i = Q5 0 by simp only [qq, h], show rr5 i = 1 by simp [rr5, h], h, a5_zero,
      Real.sin_pi_div_two]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 1 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v1, Real.sin_pi_div_four, sqrt2_half]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 2 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v2, Real.sin_neg, Real.sin_pi_div_four, mul_neg, sqrt2_half]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 3 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v3, Real.sin_neg, sin_3pi4, mul_neg, sqrt2_half]
    norm_num [Q5, pt2]
  · rw [show qq i = Q5 4 by simp only [qq, h], show rr5 i = Real.sqrt 2 by simp [rr5, h], h,
      a5_v4, Real.sin_neg, sin_5pi4, neg_neg, sqrt2_half]
    norm_num [Q5, pt2]

/-! ### Every listed point is on the frontier of the strip; the centre is interior. -/

theorem qq_y (i : ℕ) : (qq i).ofLp 1 = 1 ∨ (qq i).ofLp 1 = -1 := by
  have h : i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega
  rcases h with h | h | h | h | h <;>
    simp only [qq, h, Q5, pt2_1] <;> norm_num

theorem qq_mem (i : ℕ) : qq i ∈ Strip := by
  rcases qq_y i with h | h <;> simp only [Strip, Set.mem_setOf_eq, h] <;> norm_num

theorem qq_notint (i : ℕ) : qq i ∉ interior Strip := by
  intro hc
  obtain ⟨h1, h2⟩ := strip_interior_strict _ hc
  rcases qq_y i with h | h <;> rw [h] at h1 h2 <;> linarith

/-! ### ⛔ THE FLAT VERTEX IS REAL. -/

theorem qq_4 : qq 4 = pt2 (-1) 1 := by simp only [qq]; norm_num [Q5]
theorem qq_5 : qq 5 = pt2 0 1 := by simp only [qq]; norm_num [Q5]
theorem qq_6 : qq 6 = pt2 1 1 := by simp only [qq]; norm_num [Q5]

/-- At the flat vertex the STRICT cross product concluded by the sealed extreme-point route
(`s1_consecutive_signs`) is FALSE.  This configuration is provably outside it. -/
theorem flat_cross_zero : cross (qq 5) (qq 4) (qq 6) = 0 := by
  rw [qq_4, qq_5, qq_6]
  simp only [cross, pt2_0, pt2_1]
  ring

/-- And the flat vertex carries interior angle exactly `π`. -/
theorem flat_angle_pi : EuclideanGeometry.angle (qq 4) (qq 5) (qq 6) = Real.pi := by
  have h0 : (qq 4).ofLp 0 = (qq 5).ofLp 0 + 1 * Real.cos Real.pi := by
    rw [qq_4, qq_5, pt2_0, pt2_0, Real.cos_pi]; ring
  have h1 : (qq 4).ofLp 1 = (qq 5).ofLp 1 + 1 * Real.sin Real.pi := by
    rw [qq_4, qq_5, pt2_1, pt2_1, Real.sin_pi]; ring
  have h2 : (qq 6).ofLp 0 = (qq 5).ofLp 0 + 1 * Real.cos 0 := by
    rw [qq_6, qq_5, pt2_0, pt2_0, Real.cos_zero]; ring
  have h3 : (qq 6).ofLp 1 = (qq 5).ofLp 1 + 1 * Real.sin 0 := by
    rw [qq_6, qq_5, pt2_1, pt2_1, Real.sin_zero]; ring
  rw [polar_angle_eq_arccos_cos (qq 5) (qq 4) (qq 6) Real.pi 0 1 1 one_pos one_pos h0 h1 h2 h3,
    sub_zero, Real.cos_pi, Real.arccos_neg_one]

/-! ### ⛔ THE MODEL, END TO END. -/

theorem e1084_flat_model :
    ∑ i ∈ Finset.range 5,
        EuclideanGeometry.angle (qq i) (qq (i + 1)) (qq (i + 2)) = ((5 : ℝ) - 2) * Real.pi := by
  have hgap : ∑ i ∈ Finset.range 5, (a5 i - a5 (i + 1)) = 2 * Real.pi := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        a5_gap 0, a5_gap 1, a5_gap 2, a5_gap 3, a5_gap 4,
        gap5_0, gap5_1, gap5_2, gap5_3, gap5_4]
    ring
  simpa using
    e1084_frontier_angle_sum Strip strip_convex 5 (by norm_num) 0 strip_zero_interior
      qq a5 rr5 qq_mem qq_notint qq_per rr5_pos qq_pol0 qq_pol1
      (fun i => by rw [a5_gap i]; exact gap5_pos i)
      (fun i => by rw [a5_gap i]; exact gap5_lt_pi i)
      hgap

#print axioms e1084_frontier_angle_sum
#print axioms flat_cross_zero
#print axioms flat_angle_pi
#print axioms e1084_flat_model
