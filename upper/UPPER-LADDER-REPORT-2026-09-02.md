# erdos:1084 — `triangular_optimal_d2` — UPPER BOUND, THE LADDER MADE RUNNABLE

**Date:** 2026-09-02 · **Target:** `erdos_1084.variants.triangular_optimal_d2`,
`f 2 (3n²+3n+1) = 9n²+3n` · **Half:** upper bound `≤`, plus the two outstanding lower-bound
Finset counts.

**Artifacts:**
`oracle/evidence/msl-machine/campaigns/erdos1084-harborth-2026-09-02/upper/`
— 19 self-contained `.lean` files (1,084 lines), one obligation-DAG sidecar
(`erdos1084.upper.dag.json`, 22 nodes / 26 edges), `RUN-ON-BOX.sh`, `receipts/`,
`contract.shim.json`.

**Spend: USD 0.00.** No proposer call was made. The whole ladder was reachable
deterministically, so the USD 1.50 cap was never opened.

---

## ⛔ THE HONESTY LINE, FIRST

**There is no Lean on this machine.** Nothing below has been compiled. Every file passed
**offline structural checks only**: `import Mathlib` as the sole top-level import, the
pinned prelude present (`set_option autoImplicit false`, `set_option maxHeartbeats
400000`, `set_option maxRecDepth 4000`), balanced `() [] {} ⟨⟩ ⌊⌋` outside comments and
strings, exactly one top-level `theorem`, no tabs/CR, and the sidecar contract
`sha256(preamble + statement_line + "\n") == lean_file_sha256 == file on disk`.

Two proof statuses, and they mean different things:

| status | meaning | `sorry` |
|---|---|---|
| **LADDER_ATTEMPT** | a complete proof term is written and structurally sound; **the kernel has not seen it** | none |
| **SCAFFOLD** | the *statement* is written; the proof is one `sorry`, and the file header names in prose exactly what remains | exactly 1 |

11 of 19 files are LADDER_ATTEMPT with **zero `sorry`**. 8 are SCAFFOLDs, each named
`*_SCAFFOLD.lean`, each with its gap stated in its own header.

---

## ⭐ THE HEADLINE: THE REPORT'S "DECISIVE MISSING PRIMITIVE" WAS NOT THE BLOCKER

The campaign REPORT scoped **O2** (cyclic angular order + gap sum) as
*"NOT IN MATHLIB. THIS IS THE BLOCKER."*, 300–600 LOC, with O3 and O5 downstream of it.
Building it produced two corrections, and both are load-bearing:

**1. O2's mathematical core is six lines, and Mathlib supplies both halves.**

- the gap sum is **`Finset.sum_range_sub`** — Mathlib *has* the telescope. With the
  standard wrap convention `a m = a 0 + 2π`, `∑_{i<m} (a(i+1) − a i) = 2π` is
  `rw [Finset.sum_range_sub a m, hwrap]; ring`. That is **O02e**, 26 lines including the
  header, no `sorry`.
- the link from *geometric angle* to *argument gap* is **`arccos (cos t) ≤ |t|`**, which
  is `Real.arccos_cos` on `[0, π]` and `Real.arccos_le_pi` outside it — four tactic lines.
  That is **O02b**. And the ladder only ever needs the **inequality**, never the equality:
  `π/3 ≤ angle ≤ |Δarg|` is enough at every use site.

What actually remains of O2 is the **enumeration plumbing** — injectivity of the argument
map on the neighbour set, transport of `Finset.orderIsoOfFin` (which is *in Mathlib*) to
an `a : ℕ → ℝ`, and the wrap value. That is bookkeeping, not a missing theory, and it is
the single `sorry` in `O02_CyclicAngularOrder_SCAFFOLD.lean`.

**2. O3 does not need O2 at all.**

`O03_InteriorDegreeLeSix.lean` reaches `deg ≤ 6` by a **pigeonhole on six half-open
argument buckets of width π/3**: seven neighbours put two in one bucket, so their argument
gap is `< π/3`, so their angle is `< π/3` (O02c), contradicting `≥ π/3` (O01). No cyclic
order, no sorting, no `orderIsoOfFin`. **It carries no `sorry`** — 106 lines, the largest
LADDER_ATTEMPT in the set.

So the ladder's critical path no longer runs through O2. O2 is still wanted, but for **O06**
(the convex-polygon angle sum needs a genuine cyclic-order hypothesis), not for O03.

**3. The real largest remaining piece is O07, not O2.** O07 (`h ≥ 6k`) needs the planar
**Steiner formula** and the **isoperimetric inequality for convex bodies**, and Mathlib has
neither. The REPORT rated O07 at 400–800 LOC alongside O2 and O6; on inspection it is the
one rung with *two* missing Mathlib theories under it. A cheaper specialised route for
`h ≥ 6k` alone (direct counting over the `2k+1` lattice rows) should be scoped before the
general isoperimetric form is attempted — that recommendation is written into the file.

---

## PART 1 — THE FILES

Every file reproduces `unitDistNum`, `Metric.IsSeparated'`, the `ℝ^ n` notation and
`Erdos1084.f` **verbatim from the kernel-sealed lower-bound file** (which took them
verbatim from the formal-conjectures sources), so the `f` these theorems talk about is the
target's `f`, not a paraphrase. Files that never mention `f` still carry the same `ℝ^ n`
notation so that every statement lives in the same ambient type.

**Upstream rungs are carried as EXPLICIT HYPOTHESIS BINDERS.** `O03` binds O01's
conclusion as `h60` and the O02a+O02d+O02c chain's conclusion as `hgap`; `O11` binds the
two halves. Nothing is assumed that is not named in a binder, the DAG's `depends_on` says
which rung supplies which binder, and the composition model is the estate's own
source-inclusion (concatenate the premises' sources; the kernel re-checks from zero).

| file | statement | status | remaining obligation, one line |
|---|---|---|---|
| `O01_SixtyDegreeGap.lean` | `dist x y = 1 → dist x z = 1 → 1 ≤ dist y z → π/3 ≤ ∠ y x z` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O02a_PolarCoordinates.lean` | `x²+y²=1 → ∃ t ∈ (−π,π], cos t = x ∧ sin t = y` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O02b_ArccosCosLeAbs.lean` | `arccos (cos t) ≤ |t|` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O02c_AngleLeArgGap.lean` | unit chord `2−2cos(a−b)` ⇒ `∠ u v w ≤ |a−b|` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O02d_UnitChordIdentity.lean` | polar coords ⇒ `dist u w ² = 2 − 2 cos(a−b)` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O02e_CyclicGapSum.lean` | `a m = a 0 + 2π ⇒ ∑_{i<m}(a(i+1)−a i) = 2π` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O02f_GapBoundCardLeSix.lean` | gaps `≥ π/3` + wrap ⇒ `m ≤ 6` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O02_CyclicAngularOrder_SCAFFOLD.lean` | the assembled cyclic order at a vertex | SCAFFOLD | the enumeration plumbing: injectivity of the argument map on `D`, transport of `Finset.orderIsoOfFin` to `a : ℕ → ℝ` with the wrap value; **no missing Mathlib theory** |
| `O03_InteriorDegreeLeSix.lean` | `#(S.filter (dist v · = 1)) ≤ 6` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O04_SupportingLine_SCAFFOLD.lean` | hull point ⇒ `∃ L : ℝ²→L[ℝ]ℝ, L ≠ 0 ∧ ∀ u ∈ S, L u ≤ L v` | SCAFFOLD | the **frontier-support corollary** of `geometric_hahn_banach_point_closed`: Mathlib has strict separation of an *exterior* point, not non-strict support at a *boundary* point; a limiting argument over normalised functionals is required |
| `O05_DegreeSumBound_SCAFFOLD.lean` | `∑_{v∈S} udeg v + 2h + 6 ≤ 6n` | SCAFFOLD | the hull-vertex bound `deg v ≤ 1 + 3αᵥ/π` (O03's pigeonhole re-run inside a cone of aperture `αᵥ`), then `linarith` against O06 plus a ℕ/ℝ cast discipline |
| `O06_ConvexPolygonAngleSum_SCAFFOLD.lean` | `∑ interior angles = (h−2)π` | SCAFFOLD | a faithful Lean predicate for *"convex polygon listed in cyclic order"* (Mathlib has none; the stated hypotheses do **not** yet forbid a re-ordering), then induction on `h` by fan triangulation using `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` |
| `O07_HullSizeLowerBound_SCAFFOLD.lean` | `n = 3k²+3k+1 ⇒ 6k ≤ #hullPts S` | SCAFFOLD | the planar **Steiner formula** and the **isoperimetric inequality for convex bodies** — neither in Mathlib; or a cheaper specialised counting route for `h ≥ 6k` alone |
| `O08_Handshake.lean` | `∑ degrees = 2 · #edges` for `UD S` | LADDER_ATTEMPT | nothing mathematical; a kernel run (and an instance check) |
| `O09_UnitDistNumEqEdges_SCAFFOLD.lean` | `unitDistNum S = #edgeFinset ∧ degree = udeg` | SCAFFOLD | transcription of the already-sealed `Erdos1084.unitDistNum_image` with `Sym2.map Subtype.val` in place of `Sym2.map P`, plus a `Finset.card_bij` for the degree. **No new mathematics.** |
| `O10_Assemble.lean` | the four numeric rungs ⇒ `e ≤ 9k²+3k` | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `O11_TriangularOptimalD2.lean` | `f 2 (3k²+3k+1) = 9k²+3k` (the target) | LADDER_ATTEMPT | nothing mathematical; a kernel run |
| `L01_IdxCard_SCAFFOLD.lean` | `(idx k).card = 3k²+3k+1` | SCAFFOLD | the fibrewise fibre-size lemma (fibre over `a` has `2k+1−|a|` elements) and the `List.toFinset` nodup bookkeeping; **the arithmetic tail is proved in the preamble** |
| `L02_IdxUnitNum_SCAFFOLD.lean` | `#{q ∈ (idx k).sym2 \| qfS q = 1} = 9k²+3k` | SCAFFOLD | the ring decomposition `idx (k+1) = idx k ∪ ring (k+1)` and the count of the `18k+12` added unit pairs; **the induction-step arithmetic is proved in the preamble** |

Both lower-bound scaffolds carry a **proved** arithmetic core in their preamble
(`idx_card_arith : 3k²+3k+1 + k(k+1) = (2k+1)²` and
`idx_unitnum_step : 9k²+3k + (18k+12) = 9(k+1)²+3(k+1)`, both `by ring`), so the `sorry`
is confined to the combinatorial count and cannot silently swallow an arithmetic error.
They also mirror the sealed file's **proven header** — deliberately **without**
`open scoped Classical`, because the sealed file's own recorded trap is that a
noncomputable instance in scope kills every `decide` under `idx`.

---

## PART 2 — THE COMPILE ORDER FOR THE BOX

Each file is self-contained, so there is **no Lean-level build order**. This is the order a
human should read the results in — leaves first, so a failure lands on the smallest
statement that can carry it. `RUN-ON-BOX.sh` runs exactly this order.

```
 1 O02b_ArccosCosLeAbs.lean              ← the primitive the REPORT called the blocker
 2 O02e_CyclicGapSum.lean                ← the gap sum the REPORT called the blocker
 3 O02a_PolarCoordinates.lean
 4 O02d_UnitChordIdentity.lean
 5 O01_SixtyDegreeGap.lean
 6 O02c_AngleLeArgGap.lean
 7 O02f_GapBoundCardLeSix.lean
 8 O03_InteriorDegreeLeSix.lean          ← deg ≤ 6, no sorry, does NOT use O2
 9 O08_Handshake.lean
10 O10_Assemble.lean
11 O11_TriangularOptimalD2.lean          ← the target, le_antisymm
12 O04_SupportingLine_SCAFFOLD.lean
13 O06_ConvexPolygonAngleSum_SCAFFOLD.lean
14 O02_CyclicAngularOrder_SCAFFOLD.lean
15 O05_DegreeSumBound_SCAFFOLD.lean
16 O07_HullSizeLowerBound_SCAFFOLD.lean
17 O09_UnitDistNumEqEdges_SCAFFOLD.lean
18 L01_IdxCard_SCAFFOLD.lean
19 L02_IdxUnitNum_SCAFFOLD.lean
```

**Acceptance for each:**
LADDER_ATTEMPT → exit 0 **and** `#print axioms` clean
(`propext, Classical.choice, Quot.sound` only); `sorryAx` in one of these is a **defect**,
not a partial result. SCAFFOLD → exit 0 **with `sorryAx` present**; that is the point — a
scaffold that compiles has had its **statement** type-checked. **A scaffold that fails to
compile is a statement defect and is the more urgent bug of the two.** No `native_decide`
anywhere.

**Named API-drift risks** (the honest list of what a first box run is most likely to hit —
these are Mathlib names I could not check against the toolchain from here):
`Real.strictAntiOn_cos`, `EuclideanGeometry.law_cos` (argument order),
`Real.sin_arccos`, `abs_sub_lt_one_of_floor_eq_floor`,
`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`, `Finset.sum_range_sub`,
`SimpleGraph.sum_degrees_eq_twice_card_edges`, and the `.ofLp` / `EuclideanSpace.dist_eq`
interaction. Two known-moved names are already guarded in-file with
`first | rw [div_lt_iff …] | rw [div_lt_iff₀ …]` and the same for `div_lt_one` /
`nsmul_eq_mul`. The `.ofLp` and `EuclideanSpace.dist_eq` / `Real.sq_sqrt` /
`Fin.sum_univ_two` pattern in O02d is copied from `dist_P_sq` in the sealed file, which
already compiled on this exact box for this exact campaign.

---

## PART 3 — THE OBLIGATION DAG SIDECAR

`upper/erdos1084.upper.dag.json` — schema `obligation-dag/1.0.0`, emitted through the
estate's own `msl_obligation_dag.DagBuilder.add`, so every schema gate, the TUXEDO type
gate and the fail-closed kernel-receipt gate ran unchanged, and `validate()` /
`summarize()` computed `is_leaf` / `manufacture_target` rather than this pass asserting
them.

```
nodes 22 · edges 26 · acyclic · root binds VERBATIM · proved_kernel 1 (receipt re-verified)
type_gate ok on all 21 non-root nodes (the root is structurally exempt: frozen prose with children)
```

Every node carries `lean_preamble`, `lean_signature`, `lean_statement_line`,
`lean_file_sha256`, `lean_binders`, `type_context` and `lean_file_contract` exactly as
`msl_decompose` emits them, plus `proof_status`, `remaining_obligation`, `carries_sorry`
and `compile_order`. **The sidecar contract was re-verified at emission time**: for every
node the file was re-read from disk, split at the signature, and
`preamble + statement_line + "\n" == file` and `sha256(file) == lean_file_sha256` were
asserted. `msl_ladder` and the box runner can consume it unchanged — the **11** nodes it will
fire on (`manufacture_target: true`) are the true leaves: O01, O02a, O02b, O02d, O02e,
O08, O04, O07, O09, L01, L02.

**Edges** (`depends_on`, child → parent):

```
O02b → O02c ─┐
O02e → O02f  │
O01 ─────────┼→ O03 ──┐
O02a ────────┤        │
O02d ────────┘        ├→ O05 → O10 → O11 → ROOT
O01,O02a,O02c,O02d,O02e → O02 → O06 ──┘        ↑
O04 ──────────────────────────────────┘        │
O07, O08, O09 ────────────────────────→ O10    │
LOWER:hex_lower (PROVED_KERNEL) ─┐             │
L01 ─────────────────────────────┼→ LOWER:symbolic
L02 ─────────────────────────────┘
```

**One node is `PROVED_KERNEL`:** `erdos1084:LOWER:hex_lower`, receipt
`kernel/Erdos1084Lower.verify.json` (`status: VERIFIED`, `exitCode: 0`), source
`kernel/Erdos1084Lower.lean`. `_gate_kernel_receipt` re-read and re-verified it during
emission; if that receipt ever stops being true the node stops being produced.

### ⛔ Two things about the DAG the operator must know

1. **The campaign has no frozen `contract.json`.** `ContractSet` refuses to build without
   one. The pass therefore wrote **`upper/contract.shim.json`**, whose
   `canonical_statement` is byte-checked verbatim against
   `oracle/acquisition/.../ErdosProblems/1084.lean` before use, and pointed a *private*
   layout at a copy in the scratchpad so nothing was written outside the declared write
   scope. It is labelled `"contract_is_shim": true` in the payload and
   `"provenance": "SHIM …"` in the file. **Promoting it to the campaign root, or running
   the real ingest, is an operator move — not this pass's.**
2. **The sidecar is at `upper/erdos1084.upper.dag.json`, not in
   `oracle/evidence/msl-machine/dag/`.** `msl_ladder` reads `DAG_DIR/<problem>.dag.json`.
   Copying it there is outside this pass's write scope and would collide with a future
   full-problem DAG for `erdos1084` (this one covers the upper half only, hence the
   `.upper.` infix). The operator decides.

---

## PART 4 — WHAT CHANGED IN THE PICTURE OF THE PROBLEM

| the REPORT said (2026-09-02, morning) | what building it showed (2026-09-02, this pass) |
|---|---|
| O2 is **the** blocker, 300–600 LOC, not in Mathlib | O2's mathematical core is **two Mathlib one-liners** (`Finset.sum_range_sub`, `Real.arccos_cos`); the residue is `orderIsoOfFin` bookkeeping |
| O3 is downstream of O2 | **O3 does not use O2.** Pigeonhole on six argument buckets. Written, no `sorry` |
| O8 is free (Mathlib has handshake) | correct — but it needs a `SimpleGraph` to be free *about*, which is the `UD` definition; O9 is the real bridge and it is a **transcription of an already-sealed proof** |
| total 1,560–2,570 lines | 1,084 lines written, 11 of 19 obligations at zero `sorry`. The remaining 8 are dominated by **O07** (two missing Mathlib theories) and **O06** (a missing Lean predicate), not by O2 |

**The one thing that got *harder*, honestly:** `O06`. Writing its statement forced the
admission that Mathlib has no predicate for *"these points are the vertices of a convex
polygon in cyclic order"*, and that the natural weak hypotheses (periodicity, frontier
membership, injectivity) **do not forbid a cyclic re-ordering of the vertices** — under
which the angle sum is simply false. The file says so in its header and says **do not
weaken the statement to make it provable**. That is the rung where a wrong constant would
otherwise hide.

**The next single move**, if one thing gets run: `RUN-ON-BOX.sh` steps 1–11. Those eleven
files carry no `sorry`; if they come back exit 0 with clean axioms, the upper-bound
ladder's entire *arithmetic and angular* half is kernel-sealed in one box session, and
what is left is exactly three geometric statements (O04, O06, O07) and two transcriptions
(O09, L01/L02).

---

## Files written

| what | where |
|---|---|
| 19 Lean files | `oracle/evidence/msl-machine/campaigns/erdos1084-harborth-2026-09-02/upper/*.lean` |
| obligation DAG | `…/upper/erdos1084.upper.dag.json` |
| shim contract | `…/upper/contract.shim.json` |
| box runner | `…/upper/RUN-ON-BOX.sh` |
| receipts (empty, by design) | `…/upper/receipts/PLACEHOLDER.md` |
| generators + index | `MINE/e1084-upper/gen_lean.py`, `gen_dag.py`, `lean-index.json` |
| this report | `MINE/e1084-upper/fixer-1084-upper-report.md` |

Total 1,084 lines of Lean — which is the problem number, and is a coincidence.
