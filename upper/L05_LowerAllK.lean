/-
L05_LowerAllK -- THE COMPOSITION (close-day 2026-09-05)

The ENTIRE lower chain of erdos_1084.variants.triangular_optimal_d2 in ONE file:
the verbatim geometry of Erdos1084Lower.lean (kernel-verified 2026-09-02), the
symbolic patch count of L03_IdxCard (sealed 2026-09-05), and the symbolic unit-pair
count of L04_IdxUnitPairs (sealed 2026-09-05), composed BY SOURCE INCLUSION -- the
campaign's documented composition mode -- into

  lower_all_k :  forall k,  9k^2 + 3k <= f 2 (3k^2 + 3k + 1)

The k = 0..6 concrete seals of the lower file are corollaries.  Mechanically spliced
by build_l05.py from the three sealed sources; no proof text was retyped.
-/
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



/- ================= SPLICE: L04_IdxUnitPairs (sealed 2026-09-05) ================= -/

/-! ## Membership (proof shape probe-verified in L03) -/

lemma mem_idx (k : ℕ) (a b : ℤ) :
    (a, b) ∈ idx k ↔
      (-(k : ℤ) ≤ a ∧ a ≤ k) ∧ (-(k : ℤ) ≤ b ∧ b ≤ k) ∧
        (-(k : ℤ) ≤ a + b ∧ a + b ≤ k) := by
  constructor
  · intro h
    simp [idx] at h
    obtain ⟨⟨i, hi, j, hj, hpa, hpb⟩, h1, h2⟩ := h
    omega
  · intro h
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hs1, hs2⟩ := h
    simp [idx]
    exact ⟨⟨(a + k).toNat, by omega, (b + k).toNat, by omega, by omega, by omega⟩,
      by omega, by omega⟩

lemma mem_idx' (k : ℕ) (p : ℤ × ℤ) :
    p ∈ idx k ↔
      (-(k : ℤ) ≤ p.1 ∧ p.1 ≤ k) ∧ (-(k : ℤ) ≤ p.2 ∧ p.2 ≤ k) ∧
        (-(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ k) := by
  obtain ⟨a, b⟩ := p
  exact mem_idx k a b

/-! ## The six unit vectors of the form -/

lemma qf_eq_one_iff (u v : ℤ) :
    qf u v = 1 ↔
      (u, v) = (1, 0) ∨ (u, v) = (-1, 0) ∨ (u, v) = (0, 1) ∨ (u, v) = (0, -1) ∨
        (u, v) = (1, -1) ∨ (u, v) = (-1, 1) := by
  constructor
  · intro h
    simp only [qf] at h
    have hu1 : u ≤ 1 := by nlinarith [sq_nonneg (u + v), sq_nonneg (u - v), sq_nonneg v, sq_nonneg u]
    have hu2 : -1 ≤ u := by nlinarith [sq_nonneg (u + v), sq_nonneg (u - v), sq_nonneg v, sq_nonneg u]
    have hv1 : v ≤ 1 := by nlinarith [sq_nonneg (u + v), sq_nonneg (u - v), sq_nonneg v, sq_nonneg u]
    have hv2 : -1 ≤ v := by nlinarith [sq_nonneg (u + v), sq_nonneg (u - v), sq_nonneg v, sq_nonneg u]
    interval_cases u <;> interval_cases v <;> revert h <;> decide
  · rintro (h | h | h | h | h | h) <;>
      (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;> decide

/-! ## The three direction sets -/

def S10 (k : ℕ) : Finset (ℤ × ℤ) := (idx k).filter (fun p => (p.1 + 1, p.2) ∈ idx k)
def S01 (k : ℕ) : Finset (ℤ × ℤ) := (idx k).filter (fun p => (p.1, p.2 + 1) ∈ idx k)
def Sm11 (k : ℕ) : Finset (ℤ × ℤ) := (idx k).filter (fun p => (p.1 - 1, p.2 + 1) ∈ idx k)
def S1m1 (k : ℕ) : Finset (ℤ × ℤ) := (idx k).filter (fun p => (p.1 + 1, p.2 - 1) ∈ idx k)

/-! ## THE HARD COUNT: the (1,0) direction, fiberwise (L03 pattern) -/

lemma S10_eq (k : ℕ) :
    S10 k =
      (Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun p => -(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ (k : ℤ) - 1) := by
  ext ⟨a, b⟩
  simp only [S10, Finset.mem_filter, mem_idx, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hs1, hs2⟩, ⟨ha1', ha2'⟩, ⟨hb1', hb2'⟩, hs1', hs2'⟩
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega, by omega⟩
  · rintro ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hs1, hs2⟩
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩,
      ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩

lemma S10_row_eq (k : ℕ) (a : ℤ) :
    ((Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun p => (-(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ (k : ℤ) - 1) ∧ p.1 = a))
      = ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
          (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
            -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1)).map
          ⟨fun b => (a, b), fun x y h => ((Prod.mk.injEq a x a y).mp h).2⟩ := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_map,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hx1, hx2⟩, hy1, hy2⟩, ⟨hs1, hs2⟩, rfl⟩
    exact ⟨y, ⟨⟨hy1, hy2⟩, ⟨hx1, hx2⟩, hs1, hs2⟩, rfl, rfl⟩
  · rintro ⟨b, ⟨⟨hb1, hb2⟩, ⟨ha1, ha2⟩, hs1, hs2⟩, rfl, rfl⟩
    exact ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, ⟨hs1, hs2⟩, rfl⟩

lemma S10_row_card_neg (k : ℕ) (a : ℤ) (ha1 : -(k : ℤ) ≤ a) (ha2 : a ≤ -1) :
    ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
          -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1)).card
      = (2 * (k : ℤ) + 1 + a).toNat := by
  have hfe : ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
          -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1))
      = Finset.Icc (-(k : ℤ) - a) (k : ℤ) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfe, Int.card_Icc]
  omega

lemma S10_row_card_nonneg (k : ℕ) (a : ℤ) (ha1 : 0 ≤ a) (ha2 : a ≤ (k : ℤ) - 1) :
    ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
          -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1)).card
      = (2 * (k : ℤ) - a).toNat := by
  have hfe : ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
          -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1))
      = Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1 - a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfe, Int.card_Icc]
  omega

/-- Twice the sum of `0..n-1` (stated doubled to avoid division). -/
lemma sum_Icc_pred_mul_two (n : ℕ) :
    2 * (∑ t ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1), t) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero =>
    norm_num
  | succ m ih =>
    have hsplit : Finset.Icc (0 : ℤ) (((m + 1 : ℕ) : ℤ) - 1)
        = insert ((m : ℕ) : ℤ) (Finset.Icc (0 : ℤ) ((m : ℤ) - 1)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot : ((m : ℕ) : ℤ) ∉ Finset.Icc (0 : ℤ) ((m : ℤ) - 1) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnot, mul_add, ih]
    push_cast
    ring

lemma S10_card (k : ℕ) : (S10 k).card = 3 * k ^ 2 + k := by
  classical
  rw [S10_eq]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1))
    (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
  have hrow : ∀ a ∈ Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1),
      (((Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
          (fun p => -(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ (k : ℤ) - 1)).filter
            (fun p => p.1 = a)).card
        = ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
            (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
              -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1)).card := by
    intro a _
    rw [Finset.filter_filter, S10_row_eq, Finset.card_map]
  rw [Finset.sum_congr rfl hrow]
  have hsplit : Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1)
      = Finset.Icc (-(k : ℤ)) (-1) ∪ Finset.Icc (0 : ℤ) ((k : ℤ) - 1) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc (-(k : ℤ)) (-1)) (Finset.Icc (0 : ℤ) ((k : ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hneg : (∑ a ∈ Finset.Icc (-(k : ℤ)) (-1),
      ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
          -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1)).card)
      = ∑ a ∈ Finset.Icc (-(k : ℤ)) (-1), (2 * (k : ℤ) + 1 + a).toNat := by
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_Icc] at ha
    exact S10_row_card_neg k a ha.1 ha.2
  have hpos : (∑ a ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1),
      ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) - 1) ∧
          -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ) - 1)).card)
      = ∑ a ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1), (2 * (k : ℤ) - a).toNat := by
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_Icc] at ha
    exact S10_row_card_nonneg k a ha.1 ha.2
  rw [hneg, hpos]
  have himg : Finset.Icc (-(k : ℤ)) (-1)
      = (Finset.Icc (0 : ℤ) ((k : ℤ) - 1)).image (fun t => -1 - t) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro hx
      exact ⟨-1 - x, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      omega
  have hinj : ∀ x ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1),
      ∀ y ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1), -1 - x = -1 - y → x = y := by
    intro x _ y _ h
    omega
  rw [himg, Finset.sum_image hinj]
  have hsame : ∀ t ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1),
      (2 * (k : ℤ) + 1 + (-1 - t)).toNat = (2 * (k : ℤ) - t).toNat := by
    intro t _
    omega
  rw [Finset.sum_congr rfl hsame]
  have hbound : ∀ t ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1),
      ((2 * (k : ℤ) - t).toNat : ℤ) = 2 * (k : ℤ) - t := by
    intro t ht
    simp only [Finset.mem_Icc] at ht
    omega
  have hcard : (Finset.Icc (0 : ℤ) ((k : ℤ) - 1)).card = k := by
    rw [Int.card_Icc]
    omega
  have hz : ((∑ t ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1), (2 * (k : ℤ) - t).toNat
        + ∑ t ∈ Finset.Icc (0 : ℤ) ((k : ℤ) - 1), (2 * (k : ℤ) - t).toNat : ℕ) : ℤ)
      = ((3 * k ^ 2 + k : ℕ) : ℤ) := by
    push_cast [Nat.cast_sum]
    rw [Finset.sum_congr rfl hbound]
    have h2 := sum_Icc_pred_mul_two k
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
    simp only [nsmul_eq_mul]
    push_cast
    linarith [h2]
  exact_mod_cast hz

/-! ## Transport by the 60° rotation ρ(a,b) = (-b, a+b) and a translation -/

lemma S01_card (k : ℕ) : (S01 k).card = 3 * k ^ 2 + k := by
  classical
  have himg : S01 k = (S10 k).image (fun p => ((-p.2, p.1 + p.2) : ℤ × ℤ)) := by
    ext ⟨x, y⟩
    simp only [S01, S10, Finset.mem_filter, Finset.mem_image, mem_idx, Prod.mk.injEq]
    constructor
    · rintro ⟨hxy, hshift⟩
      refine ⟨(x + y, -x), ⟨?_, ?_⟩, by omega, by omega⟩
      · rw [mem_idx]
        omega
      · dsimp only
        omega
    · rintro ⟨⟨a, b⟩, ⟨hab, hshift⟩, hx, hy⟩
      subst hx
      subst hy
      rw [mem_idx] at hab
      dsimp only at hshift ⊢
      exact ⟨by omega, by omega⟩
  have hinj : Function.Injective (fun p : ℤ × ℤ => ((-p.2, p.1 + p.2) : ℤ × ℤ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  rw [himg, Finset.card_image_of_injective _ hinj, S10_card]

lemma S1m1_card (k : ℕ) : (S1m1 k).card = 3 * k ^ 2 + k := by
  classical
  have himg1 : Sm11 k = (S01 k).image (fun p => ((-p.2, p.1 + p.2) : ℤ × ℤ)) := by
    ext ⟨x, y⟩
    simp only [Sm11, S01, Finset.mem_filter, Finset.mem_image, mem_idx, Prod.mk.injEq]
    constructor
    · rintro ⟨hxy, hshift⟩
      refine ⟨(x + y, -x), ⟨?_, ?_⟩, by omega, by omega⟩
      · rw [mem_idx]
        omega
      · dsimp only
        omega
    · rintro ⟨⟨a, b⟩, ⟨hab, hshift⟩, hx, hy⟩
      subst hx
      subst hy
      rw [mem_idx] at hab
      dsimp only at hshift ⊢
      exact ⟨by omega, by omega⟩
  have himg2 : S1m1 k = (Sm11 k).image (fun p => ((p.1 - 1, p.2 + 1) : ℤ × ℤ)) := by
    ext ⟨x, y⟩
    simp only [S1m1, Sm11, Finset.mem_filter, Finset.mem_image, mem_idx, Prod.mk.injEq]
    constructor
    · rintro ⟨hxy, hshift⟩
      refine ⟨(x + 1, y - 1), ⟨?_, ?_⟩, by omega, by omega⟩
      · rw [mem_idx]
        omega
      · dsimp only
        omega
    · rintro ⟨⟨a, b⟩, ⟨hab, hshift⟩, hx, hy⟩
      subst hx
      subst hy
      rw [mem_idx] at hab
      dsimp only at hshift ⊢
      exact ⟨by omega, by omega⟩
  have hinjρ : Function.Injective (fun p : ℤ × ℤ => ((-p.2, p.1 + p.2) : ℤ × ℤ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  have hinjt : Function.Injective (fun p : ℤ × ℤ => ((p.1 - 1, p.2 + 1) : ℤ × ℤ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  rw [himg2, Finset.card_image_of_injective _ hinjt, himg1,
    Finset.card_image_of_injective _ hinjρ, S01_card]

/-! ## The Sym2 partition -/

def e10 (p : ℤ × ℤ) : Sym2 (ℤ × ℤ) := s(p, (p.1 + 1, p.2))
def e01 (p : ℤ × ℤ) : Sym2 (ℤ × ℤ) := s(p, (p.1, p.2 + 1))
def e1m1 (p : ℤ × ℤ) : Sym2 (ℤ × ℤ) := s(p, (p.1 + 1, p.2 - 1))

lemma e10_injective : Function.Injective e10 := by
  intro p q h
  simp [e10, Sym2.eq_iff, Prod.ext_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

lemma e01_injective : Function.Injective e01 := by
  intro p q h
  simp [e01, Sym2.eq_iff, Prod.ext_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

lemma e1m1_injective : Function.Injective e1m1 := by
  intro p q h
  simp [e1m1, Sym2.eq_iff, Prod.ext_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

def unitPairs (k : ℕ) : Finset (Sym2 (ℤ × ℤ)) :=
  (idx k).sym2.filter (fun q => qfS q = 1)

lemma qfS_mk (x y : ℤ × ℤ) : qfS s(x, y) = qf (x.1 - y.1) (x.2 - y.2) := rfl

lemma unitPairs_eq (k : ℕ) :
    unitPairs k =
      ((S10 k).image e10 ∪ (S01 k).image e01) ∪ (S1m1 k).image e1m1 := by
  classical
  ext q
  induction q using Sym2.ind with
  | _ x y =>
    simp only [unitPairs, Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_union,
      Finset.mem_image, qfS_mk]
    constructor
    · rintro ⟨⟨hx, hy⟩, hqf⟩
      rcases (qf_eq_one_iff _ _).mp hqf with h | h | h | h | h | h <;>
        simp only [Prod.mk.injEq] at h
      -- x - y = (1,0):  q = e10 y (swapped)
      · have h1 : y.1 + 1 = x.1 := by omega
        have h2 : y.2 = x.2 := by omega
        have hx' : ((y.1 + 1, y.2) : ℤ × ℤ) = x := Prod.ext_iff.mpr ⟨h1, h2⟩
        refine Or.inl (Or.inl ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩)
        · show ((y.1 + 1, y.2) : ℤ × ℤ) ∈ idx k
          rw [hx']
          exact hx
        · show s(y, ((y.1 + 1, y.2) : ℤ × ℤ)) = s(x, y)
          rw [hx']
          exact Sym2.eq_swap
      -- x - y = (-1,0): q = e10 x
      · have h1 : x.1 + 1 = y.1 := by omega
        have h2 : x.2 = y.2 := by omega
        have hy' : ((x.1 + 1, x.2) : ℤ × ℤ) = y := Prod.ext_iff.mpr ⟨h1, h2⟩
        refine Or.inl (Or.inl ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩)
        · show ((x.1 + 1, x.2) : ℤ × ℤ) ∈ idx k
          rw [hy']
          exact hy
        · show s(x, ((x.1 + 1, x.2) : ℤ × ℤ)) = s(x, y)
          rw [hy']
      -- x - y = (0,1):  q = e01 y (swapped)
      · have h1 : y.1 = x.1 := by omega
        have h2 : y.2 + 1 = x.2 := by omega
        have hx' : ((y.1, y.2 + 1) : ℤ × ℤ) = x := Prod.ext_iff.mpr ⟨h1, h2⟩
        refine Or.inl (Or.inr ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩)
        · show ((y.1, y.2 + 1) : ℤ × ℤ) ∈ idx k
          rw [hx']
          exact hx
        · show s(y, ((y.1, y.2 + 1) : ℤ × ℤ)) = s(x, y)
          rw [hx']
          exact Sym2.eq_swap
      -- x - y = (0,-1): q = e01 x
      · have h1 : x.1 = y.1 := by omega
        have h2 : x.2 + 1 = y.2 := by omega
        have hy' : ((x.1, x.2 + 1) : ℤ × ℤ) = y := Prod.ext_iff.mpr ⟨h1, h2⟩
        refine Or.inl (Or.inr ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩)
        · show ((x.1, x.2 + 1) : ℤ × ℤ) ∈ idx k
          rw [hy']
          exact hy
        · show s(x, ((x.1, x.2 + 1) : ℤ × ℤ)) = s(x, y)
          rw [hy']
      -- x - y = (1,-1): q = e1m1 y (swapped)
      · have h1 : y.1 + 1 = x.1 := by omega
        have h2 : y.2 - 1 = x.2 := by omega
        have hx' : ((y.1 + 1, y.2 - 1) : ℤ × ℤ) = x := Prod.ext_iff.mpr ⟨h1, h2⟩
        refine Or.inr ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩
        · show ((y.1 + 1, y.2 - 1) : ℤ × ℤ) ∈ idx k
          rw [hx']
          exact hx
        · show s(y, ((y.1 + 1, y.2 - 1) : ℤ × ℤ)) = s(x, y)
          rw [hx']
          exact Sym2.eq_swap
      -- x - y = (-1,1): q = e1m1 x
      · have h1 : x.1 + 1 = y.1 := by omega
        have h2 : x.2 - 1 = y.2 := by omega
        have hy' : ((x.1 + 1, x.2 - 1) : ℤ × ℤ) = y := Prod.ext_iff.mpr ⟨h1, h2⟩
        refine Or.inr ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩
        · show ((x.1 + 1, x.2 - 1) : ℤ × ℤ) ∈ idx k
          rw [hy']
          exact hy
        · show s(x, ((x.1 + 1, x.2 - 1) : ℤ × ℤ)) = s(x, y)
          rw [hy']
    · rintro ((⟨p, hp, hq⟩ | ⟨p, hp, hq⟩) | ⟨p, hp, hq⟩)
      · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        simp only [e10, Sym2.eq_iff] at hq
        rcases hq with ⟨rfl, hq2⟩ | ⟨rfl, hq2⟩ <;> subst hq2
        · refine ⟨⟨hp1, hp2⟩, ?_⟩
          show qf (p.1 - (p.1 + 1)) (p.2 - p.2) = 1
          have hA : p.1 - (p.1 + 1) = -1 := by ring
          have hB : p.2 - p.2 = 0 := by ring
          rw [hA, hB]
          decide
        · refine ⟨⟨hp2, hp1⟩, ?_⟩
          show qf ((p.1 + 1) - p.1) (p.2 - p.2) = 1
          have hA : (p.1 + 1) - p.1 = 1 := by ring
          have hB : p.2 - p.2 = 0 := by ring
          rw [hA, hB]
          decide
      · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        simp only [e01, Sym2.eq_iff] at hq
        rcases hq with ⟨rfl, hq2⟩ | ⟨rfl, hq2⟩ <;> subst hq2
        · refine ⟨⟨hp1, hp2⟩, ?_⟩
          show qf (p.1 - p.1) (p.2 - (p.2 + 1)) = 1
          have hA : p.1 - p.1 = 0 := by ring
          have hB : p.2 - (p.2 + 1) = -1 := by ring
          rw [hA, hB]
          decide
        · refine ⟨⟨hp2, hp1⟩, ?_⟩
          show qf (p.1 - p.1) ((p.2 + 1) - p.2) = 1
          have hA : p.1 - p.1 = 0 := by ring
          have hB : (p.2 + 1) - p.2 = 1 := by ring
          rw [hA, hB]
          decide
      · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        simp only [e1m1, Sym2.eq_iff] at hq
        rcases hq with ⟨rfl, hq2⟩ | ⟨rfl, hq2⟩ <;> subst hq2
        · refine ⟨⟨hp1, hp2⟩, ?_⟩
          show qf (p.1 - (p.1 + 1)) (p.2 - (p.2 - 1)) = 1
          have hA : p.1 - (p.1 + 1) = -1 := by ring
          have hB : p.2 - (p.2 - 1) = 1 := by ring
          rw [hA, hB]
          decide
        · refine ⟨⟨hp2, hp1⟩, ?_⟩
          show qf ((p.1 + 1) - p.1) ((p.2 - 1) - p.2) = 1
          have hA : (p.1 + 1) - p.1 = 1 := by ring
          have hB : (p.2 - 1) - p.2 = -1 := by ring
          rw [hA, hB]
          decide

/-- **The symbolic unit-pair count.** -/
theorem idx_unit_pairs (k : ℕ) :
    ((idx k).sym2.filter (fun q => qfS q = 1)).card = 9 * k ^ 2 + 3 * k := by
  classical
  have h : ((idx k).sym2.filter (fun q => qfS q = 1)).card = (unitPairs k).card := rfl
  rw [h, unitPairs_eq]
  have hd1 : Disjoint ((S10 k).image e10) ((S01 k).image e01) := by
    rw [Finset.disjoint_left]
    rintro q hq hq'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r, _, he⟩ := Finset.mem_image.mp hq'
    simp [e10, e01, Sym2.eq_iff, Prod.ext_iff] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hd2 : Disjoint (((S10 k).image e10) ∪ ((S01 k).image e01))
      ((S1m1 k).image e1m1) := by
    rw [Finset.disjoint_left]
    rintro q hq hq'
    obtain ⟨r, _, he⟩ := Finset.mem_image.mp hq'
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
      simp [e10, e1m1, Sym2.eq_iff, Prod.ext_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
      simp [e01, e1m1, Sym2.eq_iff, Prod.ext_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  rw [Finset.card_image_of_injective _ e10_injective,
    Finset.card_image_of_injective _ e01_injective,
    Finset.card_image_of_injective _ e1m1_injective]
  rw [S10_card, S01_card, S1m1_card]
  ring



/- ================= SPLICE: L03_IdxCard (sealed 2026-09-05) ================= -/

/-- The hexagon as a filtered product of integer intervals. -/
lemma idx_eq (k : ℕ) :
    idx k =
      (Finset.Icc (-(k : ℤ)) (k : ℤ) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun p => -(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ (k : ℤ)) := by
  ext ⟨a, b⟩
  simp only [mem_idx, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Row `a` of the hexagon: the fiber over `p.1 = a` is the filtered `b`-interval,
carried by the embedding `b ↦ (a, b)`.  The row bound is REQUIRED: without it the
map side is nonempty for `k < a ≤ 2k` while the fiber is empty (kernel-caught). -/
lemma row_eq (k : ℕ) (a : ℤ) :
    ((Finset.Icc (-(k : ℤ)) (k : ℤ) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun p => (-(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ (k : ℤ)) ∧ p.1 = a))
      = ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
          (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ)) ∧ -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ))).map
          ⟨fun b => (a, b), fun x y h => ((Prod.mk.injEq a x a y).mp h).2⟩ := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_map,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hx1, hx2⟩, hy1, hy2⟩, ⟨hs1, hs2⟩, rfl⟩
    exact ⟨y, ⟨⟨hy1, hy2⟩, ⟨hx1, hx2⟩, hs1, hs2⟩, rfl, rfl⟩
  · rintro ⟨b, ⟨⟨hb1, hb2⟩, ⟨ha1, ha2⟩, hs1, hs2⟩, rfl, rfl⟩
    exact ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, ⟨hs1, hs2⟩, rfl⟩

/-- The row length is `2k + 1 - |a|`, for rows inside the hexagon. -/
lemma row_card (k : ℕ) (a : ℤ) (ha1 : -(k : ℤ) ≤ a) (ha2 : a ≤ (k : ℤ)) :
    ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ)) ∧ -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ))).card
      = 2 * k + 1 - a.natAbs := by
  rcases le_or_gt a 0 with h | h
  · have hfe : ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ)) ∧ -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ)))
        = Finset.Icc (-(k : ℤ) - a) (k : ℤ) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hcast : (a.natAbs : ℤ) = -a := by
      omega
    rw [hfe, Int.card_Icc]
    omega
  · have hfe : ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
        (fun b => (-(k : ℤ) ≤ a ∧ a ≤ (k : ℤ)) ∧ -(k : ℤ) ≤ a + b ∧ a + b ≤ (k : ℤ)))
        = Finset.Icc (-(k : ℤ)) ((k : ℤ) - a) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hcast : (a.natAbs : ℤ) = a := by
      omega
    rw [hfe, Int.card_Icc]
    omega

/-- The absolute-value sum over a symmetric integer interval. -/
lemma sum_natAbs (k : ℕ) :
    (∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), a.natAbs) = k * (k + 1) := by
  induction k with
  | zero =>
    norm_num
  | succ n ih =>
    have hsplit :
        Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ)
          = insert (-((n + 1 : ℕ) : ℤ))
              (insert (((n + 1 : ℕ) : ℤ)) (Finset.Icc (-(n : ℕ) : ℤ) ((n : ℕ) : ℤ))) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have h1 : (-((n + 1 : ℕ) : ℤ)) ∉
        insert (((n + 1 : ℕ) : ℤ)) (Finset.Icc (-(n : ℕ) : ℤ) ((n : ℕ) : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have h2 : (((n + 1 : ℕ) : ℤ)) ∉ Finset.Icc (-(n : ℕ) : ℤ) ((n : ℕ) : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert h1, Finset.sum_insert h2, ih]
    have hA : (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 := by omega
    have hB : (((n + 1 : ℕ) : ℤ)).natAbs = n + 1 := by omega
    rw [hA, hB]
    ring

/-- **The symbolic patch count.**  For every `k`, the hexagonal patch of radius `k`
has exactly `3k² + 3k + 1` lattice points — the general form of the counts sealed
concretely at k = 0..6 in `Erdos1084Lower.lean`. -/
theorem idx_card (k : ℕ) : (idx k).card = 3 * k ^ 2 + 3 * k + 1 := by
  classical
  rw [idx_eq]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := Finset.Icc (-(k : ℤ)) (k : ℤ))
    (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
  have hstep : ∀ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (((Finset.Icc (-(k : ℤ)) (k : ℤ) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
          (fun p => -(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ (k : ℤ))).filter
            (fun p => p.1 = a)).card
        = 2 * k + 1 - a.natAbs := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    rw [Finset.filter_filter, row_eq, Finset.card_map]
    exact row_card k a ha.1 ha.2
  rw [Finset.sum_congr rfl hstep]
  -- ∑ a ∈ Icc(-k,k), (2k + 1 - a.natAbs) = 3k² + 3k + 1, computed in ℤ stepwise
  have hbound : ∀ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), a.natAbs ≤ 2 * k + 1 := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    omega
  have hcard : (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
    rw [Int.card_Icc]
    omega
  have hcast : ((∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (2 * k + 1 - a.natAbs) : ℕ) : ℤ)
      = ∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ((2 * (k : ℤ) + 1) - (a.natAbs : ℤ)) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hb := hbound a ha
    omega
  have hzsum : (∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ((2 * (k : ℤ) + 1) - (a.natAbs : ℤ)))
      = 3 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
    have habs : (∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ((a.natAbs : ℕ) : ℤ))
        = ((k * (k + 1) : ℕ) : ℤ) := by
      rw [← Nat.cast_sum, sum_natAbs]
    rw [habs]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hfin : ((∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (2 * k + 1 - a.natAbs) : ℕ) : ℤ)
      = ((3 * k ^ 2 + 3 * k + 1 : ℕ) : ℤ) := by
    rw [hcast, hzsum]
    push_cast
    ring
  exact_mod_cast hfin



/-! ## THE COMPOSITION -/

/-- **The infinite-family lower bound.**  Both counting hypotheses of `hex_lower`
discharged symbolically; the seven concrete seals become corollaries. -/
theorem lower_all_k (k : ℕ) :
    9 * k ^ 2 + 3 * k ≤ f 2 (3 * k ^ 2 + 3 * k + 1) :=
  hex_lower k (idx_card k) (idx_unit_pairs k)

end Erdos1084

#print axioms Erdos1084.lower_all_k
