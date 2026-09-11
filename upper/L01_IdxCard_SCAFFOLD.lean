import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 LOWER bound -- L01, THE HEX PATCH HAS 3k²+3k+1 POINTS (SCAFFOLD)

One of the two Finset counts that `Erdos1084.hex_lower` (KERNEL-SEALED for symbolic `k`)
still consumes as a hypothesis.  Sealing L01 and L02 turns the lower half of the target
from "proved for k = 0…6" into "proved for all k".

`idx` is reproduced VERBATIM from the kernel-sealed file, list-first, so that the `Finset`
counted here is the same `Finset` `hex_lower` quantifies over.  The header deliberately
does NOT carry `open scoped Classical`: the sealed file's own recorded trap is that a
noncomputable instance in scope kills every `decide` under `idx`.

⛔ WHAT REMAINS, EXACTLY:
    the FIBREWISE count.  `Finset.card_eq_sum_card_fiberwise` over the first coordinate;
    the fibre over `a` is `{b : max (-k, -k-a) ≤ b ≤ min (k, k-a)}`, of size
    `2k + 1 - |a|`; then `∑_{a=-k}^{k} (2k+1-|a|) = (2k+1)² - k(k+1)`.
    The arithmetic tail is `idx_card_arith` in this file's preamble and is PROVED (`ring`).
    What is missing is only the fibre-size lemma and the `List.toFinset` nodup bookkeeping
    -- roughly 100-200 lines of `Finset` combinatorics over `ℤ × ℤ`, NO new theory.

STATUS: SCAFFOLD.
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

theorem l01_idx_card (k : ℕ) : (idx k).card = 3 * k ^ 2 + 3 * k + 1 := by
  sorry
