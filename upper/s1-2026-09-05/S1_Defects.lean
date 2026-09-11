import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

/-! # erdos:1084 upper -- THE TWO STATEMENT DEFECTS IN THE FROZEN S1, KERNEL-CHECKED.

`H3_Decomposition_SCAFFOLD.lean` froze S1 with (i) ASCENDING central arguments
(`hnn : 0 ≤ a (i+1) - a i`) and (ii) `hmem` demanding only FRONTIER membership. Both are
defects with respect to the consumer `s2_sides_to_polar`, which was subsequently sealed
with the orientation hypothesis `hor : 0 < cross Y X Z`.
-/

noncomputable def cross (a b c : ℝ^ 2) : ℝ :=
  (b.ofLp 0 - a.ofLp 0) * (c.ofLp 1 - a.ofLp 1)
    - (b.ofLp 1 - a.ofLp 1) * (c.ofLp 0 - a.ofLp 0)

theorem sm0 (t : ℝ) (x : ℝ^ 2) : (t • x).ofLp 0 = t * x.ofLp 0 := rfl
theorem sm1 (t : ℝ) (x : ℝ^ 2) : (t • x).ofLp 1 = t * x.ofLp 1 := rfl
theorem ad0 (x y : ℝ^ 2) : (x + y).ofLp 0 = x.ofLp 0 + y.ofLp 0 := rfl
theorem ad1 (x y : ℝ^ 2) : (x + y).ofLp 1 = x.ofLp 1 + y.ofLp 1 := rfl

/-! ## DEFECT A -- THE ORIENTATION.  Ascending arguments make S2's `hor` FALSE.

Not "hard to prove": FALSE, at every index, for every configuration. If the listing is
sorted by ASCENDING polar argument about `v₀` with strict gaps below `π`, then
`cross (p (i+1)) (p i) v₀ < 0`, so the frozen S1's own first conclusion clause forces
`cross (p (i+1)) (p i) (p (i+2)) < 0` -- the exact negation of `s2_sides_to_polar`'s
orientation hypothesis. The ascending S1 is therefore not merely unproved: even proved in
full it could never be consumed. -/
theorem ascending_defeats_hor
    (v₀ : ℝ^ 2) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hp0 : ∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i))
    (hp1 : ∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i))
    (hposA : ∀ i, 0 < a (i + 1) - a i)
    (hltA : ∀ i, a (i + 1) - a i < Real.pi)
    (i : ℕ)
    (hfrozen : 0 < cross (p (i + 1)) (p i) v₀ * cross (p (i + 1)) (p i) (p (i + 2))) :
    cross (p (i + 1)) (p i) (p (i + 2)) < 0 := by
  have hs : 0 < Real.sin (a (i + 1) - a i) :=
    Real.sin_pos_of_pos_of_lt_pi (hposA i) (hltA i)
  have hE : cross (p (i + 1)) (p i) v₀
      = -(r i * r (i + 1) * Real.sin (a (i + 1) - a i)) := by
    simp only [cross, hp0, hp1, Real.sin_sub]; ring
  have hp := mul_pos (mul_pos (hr i) (hr (i + 1))) hs
  have hneg : cross (p (i + 1)) (p i) v₀ < 0 := by rw [hE]; linarith
  nlinarith [hfrozen, hneg]

/-! ## DEFECT B -- FRONTIER IS NOT ENOUGH.  A collinear listed triple kills every clause.

The frozen `hmem` asks only that each listed point lie on `frontier (convexHull ℝ S)`. A
point of `S` in the relative interior of a hull EDGE satisfies that and is not extreme; when
three consecutive listed points are collinear, `cross` vanishes and BOTH frozen conclusion
clauses (`0 < _ * _`) are false, as is S2's `hor`. Hence the repaired S1 must demand
EXTREME points, and does. -/
theorem collinear_kills_all_clauses (v₀ X Y Z : ℝ^ 2) (s : ℝ)
    (hY : Y = (1 - s) • X + s • Z) :
    cross Y X Z = 0 ∧ cross Y Z X = 0 ∧
    ¬ (0 < cross Y X v₀ * cross Y X Z) ∧ ¬ (0 < cross Y Z v₀ * cross Y Z X) := by
  have h1 : cross Y X Z = 0 := by
    rw [hY]; simp only [cross, ad0, ad1, sm0, sm1]; ring
  have h2 : cross Y Z X = 0 := by
    rw [hY]; simp only [cross, ad0, ad1, sm0, sm1]; ring
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h1]; simp
  · rw [h2]; simp

/-! ## Probes for the non-vacuity model of the REPAIRED S1. -/

#check @convex_closedBall
#check @norm_combo_lt_of_ne
#check @Metric.closedBall
#check @EuclideanSpace.norm_eq
#check @mem_extremePoints

#print axioms ascending_defeats_hor
#print axioms collinear_kills_all_clauses
