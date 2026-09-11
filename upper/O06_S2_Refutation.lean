import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open EuclideanGeometry

/-! # erdos:1084 upper -- MY OWN S2 STATEMENT IS FALSE. Refuted, then repaired.

`H3_Decomposition_SCAFFOLD.lean` froze obligation S2 with the side conditions written as
IFFs: `0 < cross Y X v ↔ 0 < cross Y X Z`. An iff is satisfied VACUOUSLY when both sides
are false, and every cross product vanishes on a collinear configuration -- so the frozen
S2 asserts `InsideAngleAt` for four collinear points with `v` on the far side, where it is
false. Fifth frozen-statement defect of the day, and this one is mine.

REPAIR: the hypothesis must say STRICTLY THE SAME SIDE, which is a positive PRODUCT, not
an iff.
-/

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

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

/-- The frozen S2, transcribed verbatim as a proposition. -/
def S2Statement : Prop :=
  ∀ (v X Y Z : ℝ^ 2), X ≠ Y → Z ≠ Y → v ≠ Y →
    (0 < cross Y X v ↔ 0 < cross Y X Z) →
    (0 < cross Y Z v ↔ 0 < cross Y Z X) →
    ∀ (p : ℕ → ℝ^ 2) (i : ℕ), p i = X → p (i + 1) = Y → p (i + 2) = Z →
      InsideAngleAt v p i

/-- The collinear witness: `X = (1,0)`, `Y = 0`, `Z = (2,0)`, `v = (-1,0)`.
Every cross product is `0`, so both iffs hold vacuously; but `v` is on the far side and
the polar constraints force `γ - α = 2π > π`. -/
theorem s2_statement_false : ¬ S2Statement := by
  intro H
  have hXY : pt2 1 0 ≠ pt2 0 0 := by
    intro hEq
    have := congrArg (fun z => (WithLp.ofLp z) 0) hEq
    norm_num [pt2] at this
  have hZY : pt2 2 0 ≠ pt2 0 0 := by
    intro hEq
    have := congrArg (fun z => (WithLp.ofLp z) 0) hEq
    norm_num [pt2] at this
  have hvY : pt2 (-1) 0 ≠ pt2 0 0 := by
    intro hEq
    have := congrArg (fun z => (WithLp.ofLp z) 0) hEq
    norm_num [pt2] at this
  have hc : ∀ b c : ℝ, cross (pt2 0 0) (pt2 b 0) (pt2 c 0) = 0 := by
    intro b c; simp [cross, pt2]
  obtain ⟨α, β, γ, r₁, r₂, r₃, h1, h2, h3, e1, e2, e3, e4, e5, e6, b1, b2, b3, b4, b5⟩ :=
    H (pt2 (-1) 0) (pt2 1 0) (pt2 0 0) (pt2 2 0) hXY hZY hvY
      (by rw [hc, hc]) (by rw [hc, hc])
      (fun n => if n = 0 then pt2 1 0 else if n = 1 then pt2 0 0 else pt2 2 0) 0
      (by norm_num) (by norm_num) (by norm_num)
  simp only [pt2] at e1 e2 e3 e4 e5 e6
  norm_num at e1 e2 e3 e4 e5 e6
  -- the three unit directions, read off the coordinate equations
  have hsa : Real.sin α = 0 := e2.resolve_left (ne_of_gt h1)
  have hsb : Real.sin β = 0 := e4.resolve_left (ne_of_gt h2)
  have hsg : Real.sin γ = 0 := e6.resolve_left (ne_of_gt h3)
  have sqα : (Real.cos α - 1) * (Real.cos α + 1) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq α, hsa]
  have sqβ : (Real.cos β - 1) * (Real.cos β + 1) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq β, hsb]
  have sqγ : (Real.cos γ - 1) * (Real.cos γ + 1) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq γ, hsg]
  have hca : Real.cos α = 1 := by
    rcases mul_eq_zero.mp sqα with hh | hh
    · linarith
    · exfalso; nlinarith
  have hcb : Real.cos β = -1 := by
    rcases mul_eq_zero.mp sqβ with hh | hh
    · exfalso; nlinarith
    · linarith
  have hcg : Real.cos γ = 1 := by
    rcases mul_eq_zero.mp sqγ with hh | hh
    · linarith
    · exfalso; nlinarith
  have hba : Real.cos (β - α) = -1 := by rw [Real.cos_sub, hca, hsa, hcb, hsb]; ring
  have hgb : Real.cos (γ - β) = -1 := by rw [Real.cos_sub, hcb, hsb, hcg, hsg]; ring
  have k1 : β - α = Real.pi := by
    have := Real.arccos_cos b1 b2
    rw [hba, Real.arccos_neg_one] at this
    exact this.symm
  have k2 : γ - β = Real.pi := by
    have := Real.arccos_cos b3 b4
    rw [hgb, Real.arccos_neg_one] at this
    exact this.symm
  have := Real.pi_pos
  linarith

#print axioms s2_statement_false
