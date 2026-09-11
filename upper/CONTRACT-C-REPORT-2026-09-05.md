# CONTRACT C — O02 and O06: BOTH FROZEN STATEMENTS ARE FALSE, BOTH REPAIRED AND SEALED

**Session:** MSL v2.0, MSL_MODE CLOSE, box-day 2026-09-05, absolute rounds 199–207.
**Kernel:** every run on `root@51.158.234.15`, Mathlib `919544d4`, toolchain `v4.31.0-rc1`,
`lake env lean` exit 0 **plus** `#print axioms`. Zero `sorry`, clean axiom triple
`{propext, Classical.choice, Quot.sound}` on every declaration below. No local compile.

⛔ **RECORD DEFECT, DECLARED.** The artifacts of this contract were committed inside
`2755464294 feat(e1084): O09 + L01 + L02 SEALED`, a CONCURRENT commit by the coordinating
session that swept this session's staged index. Every file and receipt landed; only this
contract's own commit message did not. This file is that message.

## 1. The two statement defects

| frozen theorem | verdict | witness | file |
|---|---|---|---|
| `o02_cyclic_angular_order` | **FALSE** | `D = (∅ : Finset (ℝ^2))` satisfies `hunit`/`hsep` vacuously and forces `a 0 = a 0 + 2π`; the gap-sum clause fails independently | `O02_EmptyRefutation.lean` |
| `o06_convex_polygon_angle_sum` | **FALSE** | four distinct **collinear** points listed out of order (abscissae 0, 2, 1, 3), all four listed angles `0`, sum `0` against the demanded `2π` | `O06_CollinearRefutation.lean` |

The O02 `sorry` is **undischargeable**: the contract's stated target cannot be met, and that
is a finding, not a failure.

The O06 defect was **predicted by the scaffold's own header** and is now a theorem. Two
mechanisms, both kernel-checked:

* `hcyclic` is a **TAUTOLOGY** — `EuclideanGeometry.angle` never exceeds `π`, so
  `EuclideanGeometry.angle_le_pi` discharges it for every listing whatsoever.
* `hfront` is satisfiable **degenerately** — the convex hull of a collinear set lies in a
  proper closed subspace, so it has empty interior (`Submodule.eq_top_of_nonempty_interior'`)
  and, being closed, is its own frontier (`IsClosed.frontier_eq`).

## 2. The repairs, all kernel-sealed

| node | statement | file |
|---|---|---|
| `O02R` | O02 **+ `D.Nonempty`**, PROVED in full | `O02_CyclicAngularOrder_Repaired.lean` |
| `O02G` | **the gap ceiling** | `O02_GapCeiling.lean` |
| `O06F` | O06 over a real cyclic-order condition (fan form) | `O06_FanAngleSum_Corrected.lean` |
| `O06M` | **the model** — the hypotheses of `O06F` are non-vacuous | `O06_SquareModel_EndToEnd.lean` |
| `O06L` | the **hypothesis-free** upper bound | `O06_FanAngleSum_UpperBound.lean` |

**O02R.** Polar arguments from O02a; injectivity of the argument map on `D` (equal argument
plus equal radius means equal point); `Finset.orderIsoOfFin` transported to `a : ℕ → ℝ` with
the wrap value at index `D.card`; interior gaps from O01 chained through O02d and O02c; and
— the move that made it work — **the wrap gap obtained by instantiating O02d/O02c at the
SHIFTED argument `a 0 + 2π`**, since `cos` and `sin` are `2π`-periodic, so the wrap gap is an
ordinary chord gap and O01 bounds it below by `π/3` like any other. No new mathematics was
needed: every prerequisite (O01, O02a–O02e) was already on disk and sorry-free.

**O02G, the gap ceiling — the session's best structural finding.** The fan form needs every
consecutive gap **at most** `π`, because `arccos (cos t) = t` holds only on `[0, π]`
(receipts `o02-gap-equals-central-angle-2026-09-05`, and the refutation at `t = 3π/2`,
`o02-gap-above-pi-breaks-central-2026-09-05`). O02 delivers the opposite bound, a **floor** of
`π/3`. The ceiling is nevertheless **free arithmetic**: with `m` gaps each `≥ π/3` summing to
`2π`, every gap is `≤ 2π − (m−1)π/3`, which is `≤ π` as soon as `m ≥ 4`. So `hcentral` is
DERIVED from the O02 floor at four or more neighbours, with no geometry at all.
**Residue: `m ≤ 3`**, where the floor genuinely permits a gap of up to `4π/3`.

**O06L.** Mathlib has **no** angle-addition-under-betweenness lemma — a grep of
`Mathlib/Geometry/Euclidean/Angle/` finds only the unconditional triangle inequality
`EuclideanGeometry.angle_le_angle_add_angle`. That inequality alone gives
`∑ interior angles ≤ (h−2)π` for **any** listing with a `2π` central total, with `hadd`
dropped entirely.

## 3. What is OPEN, at its true strength

* `hadd` — the interior angle splits at `v` — has **no derivation at any vertex count**. It is
  the exact remaining gap, and it is a Mathlib gap, not a bookkeeping one.
* `hcentral` at `m ≤ 3`.
* `O06F` is filed as a **SIBLING RESULT, never as a close of O06** (the scaffold's own order:
  do not weaken the statement to make it provable).

## 4. Instrument repair — the cable can now reach the box

Every remote launch site in `oracle/kbk/engine/lean_bridge.py` was hardcoded to `wsl.exe`, so
an operator under THE BOX LAW had **no way** to route `msl_lean_cable.py` anywhere but the
laptop. `ORACLE_LEAN_SSH=<user@host>` now routes the same script and the same stdin contract
over ssh; empty (the default) leaves the WSL path byte-identical.

⛔ One trap, recorded: **ssh joins its remote argv with spaces** and hands the result to the
login shell, so passing `["bash", "-lc", script]` as separate words ran `bash -lc test`
remotely and returned 1 — a silent false negative that reads exactly like "no Mathlib here".
The remote command must be ONE already-quoted string.

⛔ Second instrument defect, filed not fixed: the cable stamps the bare word `KERNEL_CHECKED`,
which is **not in the MSL v2.0 s.10 alphabet** (s.26.5 makes the category HARD). The category
is currently supplied by hand at report time, which is exactly where a finite certificate
becomes a universal one.

## 5. Receipts

All under `receipts-box-2026-09-05-contractC/`: seven `*.axioms.txt` kernel footprints, three
`*.cable.json` cable receipts and their obligation specs. Cable theorems under
`oracle/frontier_formalizer/cable/theorems/`.

DAG after this contract: **27 nodes, 6 `PROVED_KERNEL`, 2 `REFUTED`, 19 open.**
