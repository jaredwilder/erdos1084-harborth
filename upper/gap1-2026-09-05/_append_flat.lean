
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
