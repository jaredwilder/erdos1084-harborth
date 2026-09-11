/-
L03_IdxCard -- LADDER_ATTEMPT (authored close-day 2026-09-05, iteration 2)

THE SYMBOLIC PATCH COUNT:  (idx k).card = 3k^2 + 3k + 1  for ALL k.

Discharges, for every k at once, the hypothesis
  hc : (idx k).card = 3 * k ^ 2 + 3 * k + 1
of `hex_lower` (Erdos1084Lower.lean:228), until today sealed only at k = 0..6 by
kernel evaluation.  PUBLISHABLE-LEDGER row 8 names the two symbolic Finset counts as
the one remaining lower-half obligation; this file is the first.

Iteration note: the kernel refuted iteration 1's row lemma — stated without the row
bound it admitted rows a ∈ (k, 2k] on the map side.  The fiber is now a plain filter
(no max/min) and carries the row hypothesis explicitly.

Self-contained per campaign law: `import Mathlib`, verbatim `idx`, one exported theorem.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace Erdos1084L03

/-- VERBATIM from `Erdos1084Lower.lean` (the campaign's kernel-verified lower file). -/
def idx (k : ℕ) : Finset (ℤ × ℤ) :=
  ((((List.range (2 * k + 1)).flatMap fun i =>
      (List.range (2 * k + 1)).map fun j => ((i : ℤ) - (k : ℤ), (j : ℤ) - (k : ℤ)))).filter
    fun p => decide (-(k : ℤ) ≤ p.1 + p.2) && decide (p.1 + p.2 ≤ (k : ℤ))).toFinset

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

end Erdos1084L03

#print axioms Erdos1084L03.idx_card
