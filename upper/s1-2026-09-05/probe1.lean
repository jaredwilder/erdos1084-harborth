import Mathlib

set_option autoImplicit false

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

-- extreme points API
#check @extremePoints_convexHull_subset
#check @mem_extremePoints
#check @extremePoints_subset
#check @Set.extremePoints

-- convexity helpers
#check @Convex.segment_subset
#check @segment_subset_convexHull
#check @subset_convexHull
#check @convex_convexHull
#check @openSegment

-- arithmetic
#check @div_pos_of_neg_of_neg

-- coordinate algebra on EuclideanSpace
example (r : ℝ) (x : ℝ^ 2) : (r • x).ofLp 0 = r * x.ofLp 0 := rfl
example (x y : ℝ^ 2) : (x + y).ofLp 0 = x.ofLp 0 + y.ofLp 0 := rfl

example (x y : ℝ^ 2) (h0 : x.ofLp 0 = y.ofLp 0) (h1 : x.ofLp 1 = y.ofLp 1) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

-- openSegment membership shape
example (x y z : ℝ^ 2) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (h : a • x + b • y = z) : z ∈ openSegment ℝ x y := ⟨a, b, ha, hb, hab, h⟩

-- segment membership shape
example (x y z : ℝ^ 2) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h : a • x + b • y = z) : z ∈ segment ℝ x y := ⟨a, b, ha, hb, hab, h⟩

-- extreme point unfolding
example (A : Set (ℝ^ 2)) (x : ℝ^ 2) (hx : x ∈ A.extremePoints ℝ) :
    x ∈ A ∧ ∀ x₁ ∈ A, ∀ x₂ ∈ A, x ∈ openSegment ℝ x₁ x₂ → x₁ = x ∧ x₂ = x :=
  mem_extremePoints.mp hx
