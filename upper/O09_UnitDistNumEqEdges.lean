/-
erdos:1084 upper bound -- O09, THE COUNT BRIDGE (LADDER_ATTEMPT, discharged 2026-09-05)

Discharges O09_UnitDistNumEqEdges_SCAFFOLD: `unitDistNum S` equals the edge count of the
unit-distance graph `UD S`, and the graph degree equals `udeg`.  Statement FROZEN from the
scaffold (type-checked on the kernel this morning); the proof replays the three steps of
`Erdos1084.unitDistNum_image` from the kernel-sealed lower file with `Sym2.map Subtype.val`
in place of `Sym2.map P`, exactly as the scaffold's own header prescribes — the helper
lemmas `lift_out` and `sym2_map_injective` are VERBATIM copies from that sealed file, whose
idioms are known-good on this pinned Mathlib rev.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

/-- The number of pairs of points of a finite set `s` in a metric space that are distance
1 apart.  (VERBATIM: FormalConjecturesForMathlib/Geometry/Metric.lean) -/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-- A set `s` is `≥ eps`-separated if its elements are pairwise at distance greater or
equal to `eps` from each other.
(VERBATIM: FormalConjecturesForMathlib/Topology/MetricSpace/MetricSeparated.lean) -/
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)

end Metric

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Erdos1084

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n`
1-separated points in `ℝ^d` make.
(VERBATIM: FormalConjectures/ErdosProblems/1084.lean) -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

end Erdos1084

namespace Erdos1084Upper

/-- The unit-distance neighbours of `v` inside `S`. -/
noncomputable def nbrs (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : Finset (ℝ^ 2) :=
  {u ∈ S | dist v u = 1}

/-- The unit-distance degree of `v` in `S`. -/
noncomputable def udeg (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : ℕ := (nbrs S v).card

/-- The unit-distance graph carried by `S`.  Loopless because `dist v v = 0 ≠ 1`. -/
def UD (S : Finset (ℝ^ 2)) : SimpleGraph {x : ℝ^ 2 // x ∈ S} where
  Adj u w := dist (u : ℝ^ 2) (w : ℝ^ 2) = 1
  symm := by
    intro u w h
    rw [dist_comm]
    exact h
  loopless := ⟨fun u h => by simp [dist_self] at h⟩

/-- The points of `S` on the boundary of its convex hull. -/
noncomputable def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

/-! ## Helper lemmas, VERBATIM from the kernel-sealed `Erdos1084Lower.lean` -/

lemma sym2_map_injective {α β : Type*} {g : α → β} (hg : Function.Injective g) :
    Function.Injective (Sym2.map g) := by
  intro p q h
  induction p using Sym2.ind with | _ a b =>
  induction q using Sym2.ind with | _ c d =>
  simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hg h1, hg h2⟩
  · exact Or.inr ⟨hg h1, hg h2⟩

lemma lift_out {α β : Type*} (F : {F : α → α → β // ∀ a b, F a b = F b a}) (p : Sym2 α) :
    Sym2.lift F p = F.1 p.out.1 p.out.2 := by
  conv_lhs => rw [← Quot.out_eq p]
  rfl

end Erdos1084Upper

theorem o09_unitDistNum_eq_edges (S : Finset (ℝ^ 2)) :
    unitDistNum S = (Erdos1084Upper.UD S).edgeFinset.card ∧
      ∀ v : {x : ℝ^ 2 // x ∈ S},
        (Erdos1084Upper.UD S).degree v = Erdos1084Upper.udeg S (v : ℝ^ 2) := by
  classical
  constructor
  · -- unitDistNum S = edgeFinset.card, replaying unitDistNum_image's three steps
    unfold unitDistNum
    conv_lhs => rw [← Finset.attach_image_val (s := S), Finset.sym2_image]
    have step1 : #{x ∈ (S.attach.sym2.image (Sym2.map Subtype.val)) |
          dist x.out.1 x.out.2 = 1}
        = #{x ∈ (S.attach.sym2.image (Sym2.map Subtype.val)) |
            Sym2.lift ⟨dist, dist_comm⟩ x = 1} := by
      apply Finset.card_bij (fun a _ => a) <;>
        simp +contextual [Erdos1084Upper.lift_out]
    rw [step1, Finset.filter_image,
      Finset.card_image_of_injective _
        (Erdos1084Upper.sym2_map_injective Subtype.val_injective)]
    congr 1
    ext q
    induction q using Sym2.ind with | _ x y =>
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_attach,
      Sym2.map_mk, Sym2.lift_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Erdos1084Upper.UD, true_and, and_true]
  · -- degree = udeg, via the Subtype.val bijection
    intro v
    show ((Erdos1084Upper.UD S).neighborFinset v).card = Erdos1084Upper.udeg S (v : ℝ^ 2)
    unfold Erdos1084Upper.udeg Erdos1084Upper.nbrs
    have himg : ({u ∈ S | dist ((v : ℝ^ 2)) u = 1} : Finset (ℝ^ 2))
        = ((Erdos1084Upper.UD S).neighborFinset v).image Subtype.val := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_image, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨huS, hd⟩
        exact ⟨⟨u, huS⟩, hd, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw⟩
    rw [himg, Finset.card_image_of_injective _ Subtype.val_injective]

#print axioms o09_unitDistNum_eq_edges
