import Mathlib

set_option autoImplicit false

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

-- interior / frontier / openSegment
#check @Convex.openSegment_interior_closure_subset_interior
#check @Convex.openSegment_interior_self_subset_interior
#check @mem_interior
#check @Metric.isOpen_iff
#check @convexHull_min
#check @convex_halfspace_le
#check @interior_closedBall
#check @frontier_closedBall

example (A : Set (ℝ^ 2)) (x : ℝ^ 2) (h : x ∈ frontier A) : x ∉ interior A := h.2
example (A : Set (ℝ^ 2)) (x : ℝ^ 2) (h1 : x ∈ closure A) (h2 : x ∉ interior A) :
    x ∈ frontier A := ⟨h1, h2⟩

-- Krein-Milman / finite hull
#check @closure_convexHull_extremePoints
#check @extremePoints_convexHull_subset
#check @Set.Finite.isCompact_convexHull
#check @Set.Finite.isClosed_convexHull

-- monotonicity + trig
#check @antitone_nat_of_succ_le
#check @Real.sin_nonneg_of_nonneg_of_le_pi
#check @Real.cos_sub_pi_div_two
#check @Real.cos_add_pi_div_two
#check @Real.sin_add_pi_div_two
#check @Real.cos_add_pi
#check @Real.sin_add_pi
#check @Real.cos_pi_div_four
#check @Real.sin_pi_div_four
#check @Real.cos_periodic
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_sq_eq_abs
#check @Real.mul_self_sqrt

-- complex arg
#check @Complex.arg_nonneg_iff
#check @Complex.arg_le_pi
#check @Complex.arg_lt_pi_iff

-- coordinates
noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

example (x y : ℝ) : (pt2 x y).ofLp 0 = x := rfl
example (x y : ℝ) : (pt2 x y).ofLp 1 = y := rfl
example (x : ℝ^ 2) : ‖x‖ = Real.sqrt (x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

-- Convex from scratch on a strip
example : Convex ℝ {x : ℝ^ 2 | x.ofLp 1 ≤ 1 ∧ (-1 : ℝ) ≤ x.ofLp 1} := by
  intro x hx y hy s t hs ht hst
  refine ⟨?_, ?_⟩
  · have e : ((s • x + t • y : ℝ^ 2)).ofLp 1 = s * x.ofLp 1 + t * y.ofLp 1 := rfl
    rw [e]
    nlinarith [hx.1, hy.1]
  · have e : ((s • x + t • y : ℝ^ 2)).ofLp 1 = s * x.ofLp 1 + t * y.ofLp 1 := rfl
    rw [e]
    nlinarith [hx.2, hy.2]
