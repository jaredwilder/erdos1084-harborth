import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 LOWER bound -- L02, THE HEX PATCH HAS 9k²+3k UNIT PAIRS (SCAFFOLD)

The second Finset count `Erdos1084.hex_lower` consumes.  Purely combinatorial: no
geometry, no reals, no analysis remains in it -- `dist_P_sq` already moved the whole
question into `ℤ × ℤ`.

⛔ WHAT REMAINS, EXACTLY:
    induction on `k`.  `idx (k+1) = idx k ∪ ring (k+1)` where `ring m` is the hexagonal
    ring of `6m` points; the unit pairs added are `6(k+1)` inside the new ring plus
    `6 + 12k` spokes down to ring `k`, total `18k + 12`; and
    `9k²+3k + (18k+12) = 9(k+1)²+3(k+1)`, which is the PROVED `idx_unitnum_step` in this
    file's preamble.  What is missing is the ring decomposition of `idx` and the
    identification of the added unit pairs -- roughly 200-300 lines, NO new theory.
    (Numerically verified for k = 0…6 by the kernel `decide` calls in the sealed file, and
    for k ≤ 59 by MINE/harborth_check.py.)

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

/-- The induction step's arithmetic.  PROVED. -/
theorem idx_unitnum_step (k : ℕ) :
    9 * k ^ 2 + 3 * k + (18 * k + 12) = 9 * (k + 1) ^ 2 + 3 * (k + 1) := by ring

theorem l02_idx_unitnum (k : ℕ) :
    #{q ∈ (idx k).sym2 | qfS q = 1} = 9 * k ^ 2 + 3 * k := by
  sorry
