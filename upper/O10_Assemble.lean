import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

/-!
# erdos:1084 upper bound -- O10, THE ASSEMBLY

Pure arithmetic, subtraction-free over ℕ.  `2e = ∑ deg` (O08+O09), `∑ deg + 2h + 6 ≤ 6n`
(O05), `n = 3k²+3k+1`, `h ≥ 6k` (O07)  ⇒  `e ≤ 9k² + 3k`.

The `k ^ 2` is generalised to a fresh variable before `omega`, because `omega` is linear
and the statement is linear in `k²` once `k²` is an atom.

STATUS: LADDER_ATTEMPT -- a complete proof is written, not compiled.
-/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

theorem o10_assemble (k n h e dsum : ℕ)
    (hn : n = 3 * k ^ 2 + 3 * k + 1)
    (hhk : 6 * k ≤ h)
    (hhand : 2 * e = dsum)
    (hdegsum : dsum + 2 * h + 6 ≤ 6 * n) :
    e ≤ 9 * k ^ 2 + 3 * k := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, k ^ 2 = K := ⟨k ^ 2, rfl⟩
  rw [hK] at hn ⊢
  omega
