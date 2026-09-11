import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open scoped Classical

/-! # erdos:1084 upper -- GAP 2 CLOSED: the strict gap ceiling is a THEOREM.

`H3_Assembled.lean` and `H3G_Frontier.lean` both carry `hlt : ∀ i, a i - a (i+1) < π` as a
HYPOTHESIS; `S1-REPORT-2026-09-05.md` §5 declares it UNPROVED.  It is proved here.

THE ARGUMENT.  Suppose one consecutive central gap is `≥ π`.  The gaps are positive and sum
to `2π` over one period, so EVERY listed point then sits in the closed half-plane bounded by
the line through `v₀` normal to `a (k+1) + π/2`: its polar angle about `v₀` lies in
`[a(k+1) - π, a(k+1)]`, and the functional's value there is `r · sin(angle - a(k+1)) ≤ 0`.
The listing's hull therefore lies in that half-plane, `v₀` lies ON its bounding line, and the
covering `A ⊆ convexHull (listing)` pushes the whole set into it -- so `v₀` cannot have a ball
around it.  `v₀` interior is contradicted.

⛔ THE COVERING IS NOT A NEW ASSUMPTION.  `gap_lt_pi_hullPts` derives it from Krein-Milman
plus gap 1a (`extremePoint_mem_frontier`) and the SURJECTIVITY onto `hullPts` that
`H05_Assembly.FanInterface` already demands.  Nothing is assumed that the interface does not
already carry.
-/

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

theorem pt2_0 (x y : ℝ) : (pt2 x y).ofLp 0 = x := rfl
theorem pt2_1 (x y : ℝ) : (pt2 x y).ofLp 1 = y := rfl

theorem norm_coord (x : ℝ^ 2) : ‖x‖ = Real.sqrt (x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem norm_pt2 (x y : ℝ) : ‖pt2 x y‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [norm_coord, pt2_0, pt2_1]

noncomputable def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

theorem mem_hullPts_iff {S : Finset (ℝ^ 2)} {v : ℝ^ 2} :
    v ∈ hullPts S ↔ v ∈ S ∧ v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2))) := by
  simp only [hullPts, Finset.mem_filter]

/-! ## Gap 1a, reproduced (an extreme point is not interior). -/

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

/-! ## THE CEILING. -/

/-- ⛔ GAP 2, PROVED.  A consecutive central gap of a closed polar listing whose hull covers
`A` cannot reach `π`, because the centre is interior. -/
theorem gap_lt_pi
    (A : Set (ℝ^ 2)) (h : ℕ)
    (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ interior A)
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hper : ∀ i, p (i + h) = p i)
    (hpera : ∀ i, a (i + h) = a i - 2 * Real.pi)
    (hcov : A ⊆ convexHull ℝ (p '' Set.Icc 1 h))
    (k : ℕ) (hk : k < h) : a k - a (k + 1) < Real.pi := by
  by_contra hge
  push_neg at hge
  have hanti : Antitone a := antitone_nat_of_succ_le (fun n => by linarith [hpos n])
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.cos (a (k + 1) + Real.pi / 2) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sin (a (k + 1) + Real.pi / 2) := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ rr : ℝ, rr = v₀.ofLp 0 * c + v₀.ofLp 1 * s := ⟨_, rfl⟩
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs]
    have := Real.sin_sq_add_cos_sq (a (k + 1) + Real.pi / 2)
    linarith
  -- the half-plane
  have hHconv : Convex ℝ {x : ℝ^ 2 | x.ofLp 0 * c + x.ofLp 1 * s ≤ rr} := by
    intro x hx y hy t1 t2 ht1 ht2 ht
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have e0 : ((t1 • x + t2 • y : ℝ^ 2)).ofLp 0 = t1 * x.ofLp 0 + t2 * y.ofLp 0 := rfl
    have e1 : ((t1 • x + t2 • y : ℝ^ 2)).ofLp 1 = t1 * x.ofLp 1 + t2 * y.ofLp 1 := rfl
    rw [e0, e1]
    have hsum : t1 * rr + t2 * rr = rr := by rw [← add_mul, ht, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx ht1, mul_le_mul_of_nonneg_left hy ht2, hsum]
  -- every point of the window is in the half-plane
  have key : ∀ q, k + 1 ≤ q → q ≤ k + h →
      (p q).ofLp 0 * c + (p q).ofLp 1 * s ≤ rr := by
    intro q hq1 hq2
    have hup : a q ≤ a (k + 1) := hanti hq1
    have hlow : a (k + h) ≤ a q := hanti hq2
    have hkh : a (k + h) = a k - 2 * Real.pi := hpera k
    have hb : a (k + 1) - Real.pi ≤ a q := by rw [hkh] at hlow; linarith
    have hsin : Real.sin (a q - a (k + 1)) ≤ 0 := by
      have h1 : 0 ≤ a (k + 1) - a q := by linarith
      have h2 : a (k + 1) - a q ≤ Real.pi := by linarith
      have hnn := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
      have hneg : Real.sin (a q - a (k + 1)) = -Real.sin (a (k + 1) - a q) := by
        rw [show a q - a (k + 1) = -(a (k + 1) - a q) by ring, Real.sin_neg]
      rw [hneg]; linarith
    have hid : Real.cos (a q) * c + Real.sin (a q) * s = Real.sin (a q - a (k + 1)) := by
      have hcs2 : Real.cos (a q - (a (k + 1) + Real.pi / 2))
          = Real.cos (a q) * Real.cos (a (k + 1) + Real.pi / 2)
            + Real.sin (a q) * Real.sin (a (k + 1) + Real.pi / 2) := Real.cos_sub _ _
      rw [show a q - (a (k + 1) + Real.pi / 2) = (a q - a (k + 1)) - Real.pi / 2 by ring,
        Real.cos_sub_pi_div_two] at hcs2
      rw [hc, hs]
      linarith
    have hexp : (p q).ofLp 0 * c + (p q).ofLp 1 * s
        = rr + r q * Real.sin (a q - a (k + 1)) := by
      have hmul : r q * (Real.cos (a q) * c + Real.sin (a q) * s)
          = r q * Real.sin (a q - a (k + 1)) := by rw [hid]
      rw [hp0 q, hp1 q, hrr]
      linear_combination hmul
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hr q)) hsin
    rw [hexp]
    linarith
  have himg : (p '' Set.Icc 1 h) ⊆ {x : ℝ^ 2 | x.ofLp 0 * c + x.ofLp 1 * s ≤ rr} := by
    rintro x ⟨j, hj, rfl⟩
    obtain ⟨hj1, hj2⟩ := hj
    rcases Nat.lt_or_ge j (k + 1) with hcase | hcase
    · have hpj : p (j + h) = p j := hper j
      have hkey := key (j + h) (by omega) (by omega)
      rw [hpj] at hkey
      exact hkey
    · exact key j hcase (by omega)
  have hAsub : A ⊆ {x : ℝ^ 2 | x.ofLp 0 * c + x.ofLp 1 * s ≤ rr} :=
    hcov.trans (convexHull_min himg hHconv)
  -- but v₀ has a ball around it, and the normal direction leaves the half-plane
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior v₀ hv₀
  obtain ⟨z, hz⟩ : ∃ z : ℝ^ 2, z = v₀ + (ε / 2) • pt2 c s := ⟨_, rfl⟩
  have hnn : ‖pt2 c s‖ = 1 := by rw [norm_pt2, hcs, Real.sqrt_one]
  have hdz : dist z v₀ = ε / 2 := by
    rw [hz, dist_eq_norm, add_sub_cancel_left, norm_smul, hnn, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ ε / 2), mul_one]
  have hzA : z ∈ A :=
    interior_subset (hball (by simp only [Metric.mem_ball, hdz]; linarith))
  have hz0 : z.ofLp 0 = v₀.ofLp 0 + ε / 2 * c := by
    rw [hz]
    show v₀.ofLp 0 + (ε / 2) * (pt2 c s).ofLp 0 = _
    rw [pt2_0]
  have hz1 : z.ofLp 1 = v₀.ofLp 1 + ε / 2 * s := by
    rw [hz]
    show v₀.ofLp 1 + (ε / 2) * (pt2 c s).ofLp 1 = _
    rw [pt2_1]
  have hcontra := hAsub hzA
  simp only [Set.mem_setOf_eq, hz0, hz1] at hcontra
  have hfin : ε / 2 * (c ^ 2 + s ^ 2) = ε / 2 := by rw [hcs]; ring
  nlinarith [hcontra, hfin, hrr, hε]

/-- ⛔ GAP 2 IN THE CAMPAIGN'S VOCABULARY.  The covering hypothesis is DISCHARGED: it follows
from Krein-Milman, gap 1a, and the surjectivity onto `hullPts` that `FanInterface` already
demands.  The consumer supplies nothing new. -/
theorem gap_lt_pi_hullPts
    (S : Finset (ℝ^ 2)) (h : ℕ)
    (v₀ : ℝ^ 2) (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))))
    (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hpos : ∀ i, 0 < a i - a (i + 1))
    (hper : ∀ i, p (i + h) = p i)
    (hpera : ∀ i, a (i + h) = a i - 2 * Real.pi)
    (hsurj : ∀ w ∈ hullPts S, ∃ i < h, p (i + 1) = w)
    (k : ℕ) (hk : k < h) : a k - a (k + 1) < Real.pi := by
  have h1 : (hullPts S : Set (ℝ^ 2)) ⊆ p '' Set.Icc 1 h := by
    intro w hw
    obtain ⟨i, hi, hpi⟩ := hsurj w (Finset.mem_coe.mp hw)
    exact ⟨i + 1, ⟨by omega, by omega⟩, hpi⟩
  have hcov : convexHull ℝ (S : Set (ℝ^ 2)) ⊆ convexHull ℝ (p '' Set.Icc 1 h) :=
    (convexHull_subset_hullPts S).trans (convexHull_mono h1)
  exact gap_lt_pi (convexHull ℝ (S : Set (ℝ^ 2))) h v₀ hv₀ p a r hr hp0 hp1 hpos hper hpera
    hcov k hk

#print axioms gap_lt_pi
#print axioms gap_lt_pi_hullPts
