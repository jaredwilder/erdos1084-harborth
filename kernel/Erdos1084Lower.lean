/-
Erdos Problem 1084 -- the LOWER half of `erdos_1084.variants.triangular_optimal_d2`.

Target (DeepMind formal-conjectures, tagged `research open`):
  `f 2 (3 * n ^ 2 + 3 * n + 1) = 9 * n ^ 2 + 3 * n`

This file seals the `>=` direction by exhibiting the hexagonal patch of the triangular
lattice, entirely inside the kernel.  The definitions `unitDistNum`, `Metric.IsSeparated'`
and `f` are reproduced VERBATIM from the formal-conjectures sources
(`FormalConjecturesForMathlib/Geometry/Metric.lean`,
 `FormalConjecturesForMathlib/Topology/MetricSpace/MetricSeparated.lean`,
 `FormalConjectures/ErdosProblems/1084.lean`) so that the statement proved here is the
statement of the target, not a paraphrase.
-/
import Mathlib

open Finset Filter Metric Real
open scoped Finset ENNReal

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## Verbatim upstream definitions -/

/-- The number of pairs of points of a finite set `s` in a metric space that are distance
1 apart.  (verbatim: FormalConjecturesForMathlib/Geometry/Metric.lean) -/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]
/-- A set `s` is `>= eps`-separated if its elements are pairwise at distance greater or
equal to `eps` from each other.  (verbatim: .../MetricSpace/MetricSeparated.lean) -/
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)
end Metric

/-- (verbatim: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Erdos1084

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n`
1-separated points in `ℝ^d` make.  (verbatim: .../ErdosProblems/1084.lean) -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

/-! ## L-1 : a generic lower-bound gate for `f` -/

/-- Any admissible configuration bounds `f` from below.  This is the only place the
`iSup`-definition is unfolded; boundedness comes from the trivial pair count. -/
theorem le_f {d N : ℕ} (s : Finset (ℝ^ d)) (hcard : s.card = N)
    (hsep : IsSeparated' 1 (s : Set (ℝ^ d))) : unitDistNum s ≤ f d N := by
  have hb : ∀ t : Finset (ℝ^ d),
      (⨆ (_ : t.card = N), ⨆ (_ : IsSeparated' 1 (t : Set (ℝ^ d))), unitDistNum t)
        ≤ N * (N + 1) := by
    intro t
    refine ciSup_le' fun hc => ciSup_le' fun _ => ?_
    calc unitDistNum t ≤ #t.sym2 := Finset.card_filter_le _ _
      _ = (#t + 1).choose 2 := Finset.card_sym2 t
      _ ≤ N * (N + 1) := by
          rw [hc, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]
          exact Nat.div_le_self _ _
  have hbdd : BddAbove (Set.range fun t : Finset (ℝ^ d) =>
      ⨆ (_ : t.card = N), ⨆ (_ : IsSeparated' 1 (t : Set (ℝ^ d))), unitDistNum t) := by
    refine ⟨N * (N + 1), ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hb t
  have key := le_ciSup hbdd s
  haveI : Nonempty (s.card = N) := ⟨hcard⟩
  haveI : Nonempty (IsSeparated' 1 (s : Set (ℝ^ d))) := ⟨hsep⟩
  rwa [ciSup_const, ciSup_const] at key

/-! ## L0 : the triangular lattice, and adjacency as integer arithmetic -/

/-- The integral quadratic form of the triangular (Eisenstein) lattice. -/
def qf (u v : ℤ) : ℤ := u ^ 2 + u * v + v ^ 2

lemma qf_neg (u v : ℤ) : qf (-u) (-v) = qf u v := by unfold qf; ring

lemma qf_nonneg (u v : ℤ) : 0 ≤ qf u v := by
  unfold qf; nlinarith [sq_nonneg (2 * u + v), sq_nonneg v]

lemma qf_eq_zero_iff {u v : ℤ} : qf u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    unfold qf at h
    constructor <;> nlinarith [sq_nonneg (2 * u + v), sq_nonneg v, sq_nonneg u,
      sq_nonneg (u + 2 * v), sq_nonneg (u - v)]
  · rintro ⟨rfl, rfl⟩; unfold qf; ring

lemma one_le_qf {u v : ℤ} (h : ¬ (u = 0 ∧ v = 0)) : 1 ≤ qf u v := by
  rcases lt_or_eq_of_le (qf_nonneg u v) with h' | h'
  · omega
  · exact absurd (qf_eq_zero_iff.mp h'.symm) h

/-- The embedding of the triangular lattice into the Euclidean plane. -/
noncomputable def P (p : ℤ × ℤ) : ℝ^ 2 :=
  !₂[(p.1 : ℝ) + (p.2 : ℝ) / 2, (p.2 : ℝ) * Real.sqrt 3 / 2]

@[simp] lemma P_zero (p : ℤ × ℤ) : (P p).ofLp 0 = (p.1 : ℝ) + (p.2 : ℝ) / 2 := rfl
@[simp] lemma P_one (p : ℤ × ℤ) : (P p).ofLp 1 = (p.2 : ℝ) * Real.sqrt 3 / 2 := rfl

/-- **L0.** The squared Euclidean distance between two lattice points is the integral form. -/
lemma dist_P_sq (p q : ℤ × ℤ) :
    dist (P p) (P q) ^ 2 = ((qf (p.1 - q.1) (p.2 - q.2) : ℤ) : ℝ) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, P_zero, P_one, qf]
  push_cast
  linear_combination ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 / 4 * h3

lemma dist_P_eq_one_iff (p q : ℤ × ℤ) :
    dist (P p) (P q) = 1 ↔ qf (p.1 - q.1) (p.2 - q.2) = 1 := by
  constructor
  · intro h
    have h2 := dist_P_sq p q
    rw [h] at h2
    exact_mod_cast h2.symm
  · intro h
    have h2 := dist_P_sq p q
    rw [h] at h2
    have hnn : (0 : ℝ) ≤ dist (P p) (P q) := dist_nonneg
    push_cast at h2
    nlinarith [h2]

lemma one_le_dist_P {p q : ℤ × ℤ} (hpq : p ≠ q) : 1 ≤ dist (P p) (P q) := by
  have hne : ¬ (p.1 - q.1 = 0 ∧ p.2 - q.2 = 0) := by
    rintro ⟨h1, h2⟩
    exact hpq (Prod.ext (by omega) (by omega))
  have h1 : (1 : ℤ) ≤ qf (p.1 - q.1) (p.2 - q.2) := one_le_qf hne
  have h2 := dist_P_sq p q
  have hnn : (0 : ℝ) ≤ dist (P p) (P q) := dist_nonneg
  have hc : (1 : ℝ) ≤ ((qf (p.1 - q.1) (p.2 - q.2) : ℤ) : ℝ) := by exact_mod_cast h1
  nlinarith [h2, hc]

lemma P_injective : Function.Injective P := by
  intro p q h
  by_contra hpq
  have := one_le_dist_P hpq
  rw [h, dist_self] at this
  linarith

/-! ## Lattice sets and the transfer of the count -/

/-- The hexagonal patch of radius `k` in axial coordinates:
`{(a,b) : |a| ≤ k, |b| ≤ k, |a+b| ≤ k}`.

Built list-first on purpose.  Under `import Mathlib` the `Finset.Icc` instance path for `Int`
resolves through `_root_.instConditionallyCompleteLinearOrder`, which is noncomputable and
would make every `decide` below impossible. -/
def idx (k : ℕ) : Finset (ℤ × ℤ) :=
  ((((List.range (2 * k + 1)).flatMap fun i =>
      (List.range (2 * k + 1)).map fun j => ((i : ℤ) - (k : ℤ), (j : ℤ) - (k : ℤ)))).filter
    fun p => decide (-(k : ℤ) ≤ p.1 + p.2) && decide (p.1 + p.2 ≤ (k : ℤ))).toFinset

/-- The hexagonal patch as a point set in the plane. -/
noncomputable def hex (k : ℕ) : Finset (ℝ^ 2) := (idx k).image P

/-- The form, lifted to unordered pairs of lattice points. -/
def qfS : Sym2 (ℤ × ℤ) → ℤ :=
  Sym2.lift ⟨fun p q => qf (p.1 - q.1) (p.2 - q.2), by
    intro a b
    simp only [qf]
    ring⟩

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

/-- **The transfer.**  The unit-distance count of an embedded lattice set is the integer
count of index pairs whose form value is `1`. -/
lemma unitDistNum_image (T : Finset (ℤ × ℤ)) :
    unitDistNum (T.image P) = #{q ∈ T.sym2 | qfS q = 1} := by
  classical
  unfold unitDistNum
  rw [Finset.sym2_image]
  have step1 : #{x ∈ (T.sym2.image (Sym2.map P)) | dist x.out.1 x.out.2 = 1}
      = #{x ∈ (T.sym2.image (Sym2.map P)) | Sym2.lift ⟨dist, dist_comm⟩ x = 1} := by
    apply Finset.card_bij (fun a _ => a) <;> simp +contextual [lift_out]
  rw [step1, Finset.filter_image,
    Finset.card_image_of_injective _ (sym2_map_injective P_injective)]
  apply Finset.card_bij (fun a _ => a)
  · intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    refine ⟨ha.1, ?_⟩
    induction a using Sym2.ind with | _ x y =>
    simp only [Sym2.map_mk, Sym2.lift_mk] at ha ⊢
    exact (dist_P_eq_one_iff x y).mp ha.2
  · intro a _ b _ h; exact h
  · intro b hb
    refine ⟨b, ?_, rfl⟩
    simp only [Finset.mem_filter, qfS] at hb ⊢
    refine ⟨hb.1, ?_⟩
    induction b using Sym2.ind with | _ x y =>
    simp only [Sym2.map_mk, Sym2.lift_mk] at hb ⊢
    exact (dist_P_eq_one_iff x y).mpr hb.2

/-! ## The hexagonal patch is admissible -/

lemma hex_card (k : ℕ) : (hex k).card = (idx k).card :=
  Finset.card_image_of_injective _ P_injective

lemma hex_separated (k : ℕ) : IsSeparated' 1 ((hex k : Finset (ℝ^ 2)) : Set (ℝ^ 2)) := by
  rintro x hx y hy hxy
  simp only [hex, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨p, _, rfl⟩ := hx
  obtain ⟨q, _, rfl⟩ := hy
  have hpq : p ≠ q := by rintro rfl; exact hxy rfl
  rw [edist_dist]
  exact ENNReal.one_le_ofReal.mpr (one_le_dist_P hpq)

lemma hex_unitDistNum (k : ℕ) : unitDistNum (hex k) = #{q ∈ (idx k).sym2 | qfS q = 1} :=
  unitDistNum_image (idx k)

/-- **The lower-bound gate.**  Given the two finite counts for a concrete `k`, the
hexagonal patch witnesses `f 2 (3k^2+3k+1) >= 9k^2+3k`. -/
theorem hex_lower (k : ℕ)
    (hc : (idx k).card = 3 * k ^ 2 + 3 * k + 1)
    (he : #{q ∈ (idx k).sym2 | qfS q = 1} = 9 * k ^ 2 + 3 * k) :
    9 * k ^ 2 + 3 * k ≤ f 2 (3 * k ^ 2 + 3 * k + 1) := by
  have h := le_f (hex k) (by rw [hex_card, hc]) (hex_separated k)
  rwa [hex_unitDistNum, he] at h

/-! ## Concrete seals

`hex_lower` reduces the target's `≥` direction to two finite integer counts over the
explicit lattice patch.  Each is discharged by kernel evaluation: no `native_decide`, no
floating point, no numerics -- the only bridge to the real plane is `dist_P_sq`. -/

theorem lower_k0 : 9 * 0 ^ 2 + 3 * 0 ≤ f 2 (3 * 0 ^ 2 + 3 * 0 + 1) :=
  hex_lower 0 (by decide) (by decide)

theorem lower_k1 : 9 * 1 ^ 2 + 3 * 1 ≤ f 2 (3 * 1 ^ 2 + 3 * 1 + 1) :=
  hex_lower 1 (by decide) (by decide)

theorem lower_k2 : 9 * 2 ^ 2 + 3 * 2 ≤ f 2 (3 * 2 ^ 2 + 3 * 2 + 1) :=
  hex_lower 2 (by decide) (by decide)

theorem lower_k3 : 9 * 3 ^ 2 + 3 * 3 ≤ f 2 (3 * 3 ^ 2 + 3 * 3 + 1) :=
  hex_lower 3 (by decide) (by decide)

theorem lower_k4 : 9 * 4 ^ 2 + 3 * 4 ≤ f 2 (3 * 4 ^ 2 + 3 * 4 + 1) :=
  hex_lower 4 (by decide) (by decide)

theorem lower_k5 : 9 * 5 ^ 2 + 3 * 5 ≤ f 2 (3 * 5 ^ 2 + 3 * 5 + 1) :=
  hex_lower 5 (by decide) (by decide)

theorem lower_k6 : 9 * 6 ^ 2 + 3 * 6 ≤ f 2 (3 * 6 ^ 2 + 3 * 6 + 1) :=
  hex_lower 6 (by decide) (by decide)

/-! ### Human-readable forms

`n` points in the plane, pairwise at distance `≥ 1`, realising the stated number of
distances exactly `1`. -/

theorem lower_7   : 12  ≤ f 2 7   := by simpa using lower_k1
theorem lower_19  : 42  ≤ f 2 19  := by simpa using lower_k2
theorem lower_37  : 90  ≤ f 2 37  := by simpa using lower_k3
theorem lower_61  : 156 ≤ f 2 61  := by simpa using lower_k4
theorem lower_91  : 240 ≤ f 2 91  := by simpa using lower_k5
theorem lower_127 : 342 ≤ f 2 127 := by simpa using lower_k6

end Erdos1084

/-! ## Axiom qualification -/
#print axioms Erdos1084.le_f
#print axioms Erdos1084.dist_P_sq
#print axioms Erdos1084.unitDistNum_image
#print axioms Erdos1084.hex_lower
#print axioms Erdos1084.lower_k0
#print axioms Erdos1084.lower_k1
#print axioms Erdos1084.lower_k2
#print axioms Erdos1084.lower_k3
#print axioms Erdos1084.lower_k4
#print axioms Erdos1084.lower_k5
#print axioms Erdos1084.lower_k6
#print axioms Erdos1084.lower_127
