import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# erdos:1084 upper -- O02 STATEMENT DEFECT, kernel-exhibited

`o02_cyclic_angular_order` as frozen in `O02_CyclicAngularOrder_SCAFFOLD.lean` is FALSE.
`D = (∅ : Finset (ℝ^2))` satisfies both hypotheses vacuously and forces the wrap clause
`a D.card = a 0 + 2 * π` to read `a 0 = a 0 + 2 * π`, i.e. `0 = 2π`.
The sum clause `∑ i ∈ range 0, _ = 2π` fails independently for the same reason.
-/

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

/-- The frozen O02 statement, verbatim, as a proposition. -/
def O02Statement : Prop :=
  ∀ (v : ℝ^ 2) (D : Finset (ℝ^ 2)),
    (∀ u ∈ D, dist v u = 1) →
    (∀ u ∈ D, ∀ w ∈ D, u ≠ w → 1 ≤ dist u w) →
    ∃ a : ℕ → ℝ,
      (∀ i, i < D.card → -Real.pi < a i ∧ a i ≤ Real.pi) ∧
      (∀ i, i + 1 < D.card → a i < a (i + 1)) ∧
      a D.card = a 0 + 2 * Real.pi ∧
      (∀ i, i < D.card → Real.pi / 3 ≤ a (i + 1) - a i) ∧
      ∑ i ∈ Finset.range D.card, (a (i + 1) - a i) = 2 * Real.pi

/-- Refutation via the wrap clause at the empty neighbour set. -/
theorem o02_statement_false_wrap : ¬ O02Statement := by
  intro h
  obtain ⟨a, -, -, hwrap, -, -⟩ := h 0 ∅ (by simp) (by simp)
  rw [Finset.card_empty] at hwrap
  have hpi := Real.pi_pos
  linarith

/-- Independent refutation via the gap-sum clause at the empty neighbour set. -/
theorem o02_statement_false_sum : ¬ O02Statement := by
  intro h
  obtain ⟨a, -, -, -, -, hsum⟩ := h 0 ∅ (by simp) (by simp)
  rw [Finset.card_empty, Finset.range_zero, Finset.sum_empty] at hsum
  have hpi := Real.pi_pos
  linarith

#print axioms o02_statement_false_wrap
#print axioms o02_statement_false_sum
