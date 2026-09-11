import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-!
# erdos:1084 LOWER bound -- L02, THE HEX PATCH HAS 9k²+3k UNIT PAIRS (SEALED)

The second Finset count `Erdos1084.hex_lower` consumes.  Purely combinatorial: no
geometry, no reals, no analysis remains in it -- `dist_P_sq` already moved the whole
question into `ℤ × ℤ`.

✅ THE SORRY IS DISCHARGED (2026-09-05).  Nothing about the FROZEN statement changed:
    `theorem l02_idx_unitnum (k : ℕ) : #{q ∈ (idx k).sym2 | qfS q = 1} = 9 * k ^ 2 + 3 * k`
    is byte-identical to the scaffold's.  The proof is SOURCE-INCLUDED from
    `L04_IdxUnitPairs.lean` (kernel-sealed the same day, axioms
    [propext, Classical.choice, Quot.sound]), whose exported theorem
    `Erdos1084L04.idx_unit_pairs` states the same count over the same verbatim `idx`
    and `qfS`.  The whole L04 chain is carried into the `Erdos1084L02` namespace and
    re-pointed at this file's ROOT `idx` / `qf` / `qfS`, which are the constants the
    frozen statement names.

    ⛔ THE ROUTE IS NOT THE ONE THE SCAFFOLD PREDICTED, and that is the finding.
    The scaffold projected induction on `k` via a ring decomposition
    `idx (k+1) = idx k ∪ ring (k+1)`, adding `18k + 12` unit pairs per step
    (that is `idx_unitnum_step`, kept verbatim below and still PROVED).  L04 closes the
    count WITHOUT any induction on the hexagon: one hard fiberwise count in the (1,0)
    direction (`3k² + k`, the L03 machinery), then the 60° lattice rotation
    ρ(a,b) = (-b, a+b) plus one translation transports it to the other two directions,
    and the `Sym2` filter is the disjoint union of the three direction images:
    3·(3k² + k) = 9k² + 3k.  `idx_unitnum_step` is therefore now an unused-but-true
    preamble lemma, not a step of the live proof.

    set_option deltas vs the scaffold: `maxHeartbeats 400000 → 1600000`,
    `maxRecDepth 4000 → 8000`, matching the budget the sealed L04 actually consumed.
    Both bear on termination, never on soundness; the FROZEN statement is untouched.

STATUS: SEALED (pending this file's own kernel receipt).
-/

open Finset Filter Metric Real
open scoped Finset ENNReal

/-- The integral quadratic form of the triangular (Eisenstein) lattice.
(VERBATIM: Erdos1084Lower.lean, kernel-sealed 2026-09-02,
 sha256 eabb57f873d36bca83d24b3e7616fe053627179e8b82a05fff730820b97485ac) -/
def qf (u v : ℤ) : ℤ := u ^ 2 + u * v + v ^ 2

/-- The hexagonal patch of radius `k` in axial coordinates:
`{(a,b) : |a| ≤ k, |b| ≤ k, |a+b| ≤ k}`.

Built list-first on purpose.  Under `import Mathlib` the `Finset.Icc` instance path for
`Int` resolves through `_root_.instConditionallyCompleteLinearOrder`, which is
noncomputable and would make every `decide` below impossible.
(VERBATIM: Erdos1084Lower.lean) -/
def idx (k : ℕ) : Finset (ℤ × ℤ) :=
  ((((List.range (2 * k + 1)).flatMap fun i =>
      (List.range (2 * k + 1)).map fun j => ((i : ℤ) - (k : ℤ), (j : ℤ) - (k : ℤ)))).filter
    fun p => decide (-(k : ℤ) ≤ p.1 + p.2) && decide (p.1 + p.2 ≤ (k : ℤ))).toFinset

/-- The form, lifted to unordered pairs of lattice points.  (VERBATIM: Erdos1084Lower.lean) -/
def qfS : Sym2 (ℤ × ℤ) → ℤ :=
  Sym2.lift ⟨fun p q => qf (p.1 - q.1) (p.2 - q.2), by
    intro a b
    simp only [qf]
    ring⟩

/-- The induction step's arithmetic.  PROVED.  (Kept verbatim from the scaffold; the
sealed proof below reaches the same count by symmetry transport instead of induction,
so this lemma is now a true preamble fact rather than a live step.) -/
theorem idx_unitnum_step (k : ℕ) :
    9 * k ^ 2 + 3 * k + (18 * k + 12) = 9 * (k + 1) ^ 2 + 3 * (k + 1) := by ring

namespace Erdos1084L02

/-! ## SOURCE-INCLUDED from `L04_IdxUnitPairs.lean` (kernel-sealed 2026-09-05).
Each declaration below is the L04 declaration verbatim, re-pointed at this file's
root `qf` / `idx` / `qfS`. -/

lemma qf_neg (u v : ℤ) : qf (-u) (-v) = qf u v := by unfold qf; ring

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

end Erdos1084L02

/-- **The symbolic unit-pair count** (FROZEN statement, verbatim from the scaffold).
Proof source-included from `Erdos1084L04.idx_unit_pairs`. -/
theorem l02_idx_unitnum (k : ℕ) :
    #{q ∈ (idx k).sym2 | qfS q = 1} = 9 * k ^ 2 + 3 * k := by
  classical
  have h : #{q ∈ (idx k).sym2 | qfS q = 1} = (Erdos1084L02.unitPairs k).card := rfl
  rw [h, Erdos1084L02.unitPairs_eq]
  have hd1 : Disjoint ((Erdos1084L02.S10 k).image Erdos1084L02.e10)
      ((Erdos1084L02.S01 k).image Erdos1084L02.e01) := by
    rw [Finset.disjoint_left]
    rintro q hq hq'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r, _, he⟩ := Finset.mem_image.mp hq'
    simp [Erdos1084L02.e10, Erdos1084L02.e01, Sym2.eq_iff, Prod.ext_iff] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hd2 : Disjoint (((Erdos1084L02.S10 k).image Erdos1084L02.e10)
      ∪ ((Erdos1084L02.S01 k).image Erdos1084L02.e01))
      ((Erdos1084L02.S1m1 k).image Erdos1084L02.e1m1) := by
    rw [Finset.disjoint_left]
    rintro q hq hq'
    obtain ⟨r, _, he⟩ := Finset.mem_image.mp hq'
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
      simp [Erdos1084L02.e10, Erdos1084L02.e1m1, Sym2.eq_iff, Prod.ext_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
      simp [Erdos1084L02.e01, Erdos1084L02.e1m1, Sym2.eq_iff, Prod.ext_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  rw [Finset.card_image_of_injective _ Erdos1084L02.e10_injective,
    Finset.card_image_of_injective _ Erdos1084L02.e01_injective,
    Finset.card_image_of_injective _ Erdos1084L02.e1m1_injective]
  rw [Erdos1084L02.S10_card, Erdos1084L02.S01_card, Erdos1084L02.S1m1_card]
  ring

#print axioms l02_idx_unitnum
