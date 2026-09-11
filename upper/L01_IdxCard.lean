import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-!
# erdos:1084 LOWER bound -- L01, THE HEX PATCH HAS 3k²+3k+1 POINTS (SEALED)

One of the two Finset counts that `Erdos1084.hex_lower` (KERNEL-SEALED for symbolic `k`)
still consumes as a hypothesis.  Sealing L01 and L02 turns the lower half of the target
from "proved for k = 0…6" into "proved for all k".

`idx` is reproduced VERBATIM from the kernel-sealed file, list-first, so that the `Finset`
counted here is the same `Finset` `hex_lower` quantifies over.  The header deliberately
does NOT carry `open scoped Classical`: the sealed file's own recorded trap is that a
noncomputable instance in scope kills every `decide` under `idx`.

✅ THE SORRY IS DISCHARGED (2026-09-05).  Nothing about the FROZEN statement changed:
    `theorem l01_idx_card (k : ℕ) : (idx k).card = 3 * k ^ 2 + 3 * k + 1`
    is byte-identical to the scaffold's.  The proof is SOURCE-INCLUDED from
    `L03_IdxCard.lean` (kernel-sealed the same day, axioms
    [propext, Classical.choice, Quot.sound]), whose exported theorem
    `Erdos1084L03.idx_card` has exactly this statement over the same verbatim `idx`.
    The L03 helper chain (`mem_idx` → `idx_eq` → `row_eq` → `row_card` → `sum_natAbs`)
    is carried into the `Erdos1084L01` namespace and re-points at this file's ROOT `idx`,
    which is the `idx` the frozen statement names.

    The route the scaffold predicted is the route that was taken: fibrewise count over
    the first coordinate (`Finset.card_eq_sum_card_fiberwise`), fibre size `2k + 1 - |a|`,
    then `∑_{a=-k}^{k} (2k+1-|a|) = (2k+1)² - k(k+1)`.  `idx_card_arith` below is kept
    verbatim from the scaffold; the spliced proof does the same arithmetic inline in ℤ.

    set_option deltas vs the scaffold: `maxHeartbeats 400000 → 800000`, matching the
    budget the sealed L03 actually consumed.  Heartbeats bear on termination, never on
    soundness, and the FROZEN statement is untouched.

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

/-- The arithmetic tail of the fibrewise count, subtraction-free.  PROVED. -/
theorem idx_card_arith (k : ℕ) :
    3 * k ^ 2 + 3 * k + 1 + k * (k + 1) = (2 * k + 1) ^ 2 := by ring

namespace Erdos1084L01

/-! ## SOURCE-INCLUDED from `L03_IdxCard.lean` (kernel-sealed 2026-09-05).
Each lemma below is the L03 lemma verbatim, re-pointed at this file's root `idx`. -/

/-- Membership in `idx k` is exactly the three interval conditions of the hexagon. -/
lemma mem_idx (k : ℕ) (a b : ℤ) :
    (a, b) ∈ idx k ↔
      (-(k : ℤ) ≤ a ∧ a ≤ k) ∧ (-(k : ℤ) ≤ b ∧ b ≤ k) ∧
        (-(k : ℤ) ≤ a + b ∧ a + b ≤ k) := by
  -- The elaborator-probed normal form of `simp [idx]` at the hypothesis is
  --   (∃ i ≤ 2k, ∃ j ≤ 2k, ↑i - ↑k = a ∧ ↑j - ↑k = b) ∧ -↑k ≤ a+b ∧ a+b ≤ ↑k
  -- (probe receipt: /root/peer/probe_memidx2.lean on the box, 2026-09-05).
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

end Erdos1084L01

/-- **The symbolic patch count** (FROZEN statement, verbatim from the scaffold).
For every `k`, the hexagonal patch of radius `k` has exactly `3k² + 3k + 1` lattice
points — the general form of the counts sealed concretely at k = 0..6 in
`Erdos1084Lower.lean`.  Proof source-included from `Erdos1084L03.idx_card`. -/
theorem l01_idx_card (k : ℕ) : (idx k).card = 3 * k ^ 2 + 3 * k + 1 := by
  classical
  rw [Erdos1084L01.idx_eq]
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
    rw [Finset.filter_filter, Erdos1084L01.row_eq, Finset.card_map]
    exact Erdos1084L01.row_card k a ha.1 ha.2
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
      rw [← Nat.cast_sum, Erdos1084L01.sum_natAbs]
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

#print axioms l01_idx_card
