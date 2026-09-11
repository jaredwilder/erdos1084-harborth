# erdos:1084 — `triangular_optimal_d2` — fixer report

**Date:** 2026-09-02 · **Target:** `erdos_1084.variants.triangular_optimal_d2`
(`oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/1084.lean`, tagged
`@[category research open]`)

**Statement:** `f 2 (3 * n ^ 2 + 3 * n + 1) = 9 * n ^ 2 + 3 * n`, where
`f d n = ⨆ (s : Finset (ℝ^d)) (_ : s.card = n) (_ : IsSeparated' 1 ↑s), unitDistNum s`.

**Bottom line:**
- **Prior art: `KNOWN_THEOREM`.** Harborth 1974. The scan's hunch (`MINE/pool-wang-top.json`, row 1) was right, and the "open" tag is a mislabel.
- **Lower bound `≥`: KERNEL-SEALED for k = 0…6** (exit 0, 24.43 s, axioms clean, no `native_decide`). The general-k theorem `hex_lower` is proved for **symbolic k**; only its two finite integer counts are per-k.
- **Upper bound `≤`: not attempted.** Obligation ladder scoped below; ~1,500–2,600 lines, and the *decisive* missing Mathlib primitive is named.

---

## PART 1 — PRIOR ART

### Verdict: `KNOWN_THEOREM`

**Citation.** Heiko Harborth, *"Lösung zu Problem 664A"*, **Elemente der Mathematik 29 (1974), 14–15**.
Harborth proved that a **penny graph** on `n` vertices has at most

```
   ⌊ 3n − √(12n − 3) ⌋   edges,
```

and that the bound is **sharp**, attained by a hexagonal piece of the regular triangular
lattice. A penny graph is exactly the object in the Lean file: points pairwise at distance
`≥ 1` (`IsSeparated' 1`), edges the pairs at distance exactly `1` (`unitDistNum`). So
Harborth's `e(n)` **is** `f 2 n`, verbatim.

### Does the floor bound give the *equality* at n = 3k²+3k+1? Yes — and exactly there.

The scan checked `k ≤ 59` numerically (`MINE/harborth_check.py`). The general algebra, which
that script did not state:

```
n = 3k² + 3k + 1
  ⇒ 12n − 3 = 36k² + 36k + 12 − 3 = 36k² + 36k + 9 = (6k + 3)²
  ⇒ √(12n − 3) = 6k + 3          (exact, an integer — the floor is a no-op)
  ⇒ 3n − √(12n−3) = (9k² + 9k + 3) − (6k + 3) = 9k² + 3k.
```

Stronger, and worth recording: the centred hexagonal numbers are **precisely** the `n` at
which the radicand is a perfect square. If `12n − 3 = m²` then `m` is odd, `m = 2t+1`, so
`4t² + 4t + 1 = 12n − 3`, i.e. `n = (t² + t + 1)/3`, which forces `t ≡ 1 (mod 3)`; writing
`t = 3k+1` gives `n = 3k² + 3k + 1`. So `n = 3k²+3k+1` are exactly the `n` where Harborth's
bound is an integer with no truncation — which is why the conjecture is stated at those `n`
and nowhere else.

Combining: **upper** `f 2 n ≤ ⌊3n−√(12n−3)⌋ = 9k²+3k` (Harborth) with **lower**
`f 2 n ≥ 9k²+3k` (the hexagonal patch, which is Harborth's own sharpness example) gives the
equality. The Lean statement is therefore a **corollary of a 1974 theorem**, not an open
problem. The `research open` tag in the DeepMind corpus is a **mislabel** — plausibly because
the file's own docstring paraphrases Erdős's 1975 *conjecture* (`[Er75f]`) and never picks up
that the conjecture was settled the year before it was restated.

**Also relevant (the modern descendant):** the same bound for **matchstick** graphs (the
weaker hypothesis: unit edges, no minimum-distance condition) was Harborth's *conjecture*, and
was proved by **Lavollée & Swanepoel**, *"A Tight Bound for the Number of Edges of Matchstick
Graphs"*, Discrete & Computational Geometry (2023) — arXiv:2209.09800. This is the paper the
estate's own novelty door retrieved (below).

### Estate tooling receipt — and an honest note on its limits

```
python -m oracle.reality.noveltyforge.cli acquire --claim nf-mission-1084.json --out nf-corpus-1084.json
→ {"acquired": 30, "paper_count": 30, "corpus_source": "auto_acquired_litacq_patents"}
   acquisition_receipt_sha256 = 2a3e351e3e72774bd4260916435da9825397603709d64db1a488d21a5a023b46
```
Receipts: `oracle/evidence/msl-machine/campaigns/erdos1084-harborth-2026-09-02/prior-art/`.

**The door ran and returned a real corpus, but it is a weak instrument on this claim.** Of 30
retrieved papers, **exactly one is on target** — the Lavollée–Swanepoel 2023 tight-bound paper.
The other 29 are topic-level ("Handbook of Discrete and Computational Geometry", "Lectures on
Discrete Geometry", …): its query expansion is tuned for the bio/materials lanes and degrades
to the field name on a pure combinatorial-geometry claim. **It did not surface Harborth 1974**
(a two-page 1974 German note in *Elemente der Mathematik*, essentially unindexed). The decisive
attribution here comes from WebSearch plus the arithmetic identity above — I am labelling that
honestly rather than dressing the noveltyforge output up as the receipt it is not.
`erdosproblems.com/1084` returns 403 from this box, as the scan recorded; `literature_guard.py`
was not bypassed at any point.

### Why this is still worth doing

Even at `KNOWN_THEOREM`, this is the **"prior art exists but the machine proved it"** pattern.
Nothing in the formal record contains a machine-checked proof of any part of this statement;
the DeepMind file carries `sorry`. A kernel-sealed half of a variant that the reference corpus
itself calls `research open` is a real artifact — and the mislabel is itself a finding worth
sending upstream.

---

## PART 2 — THE LOWER BOUND, KERNEL-SEALED

**Artifact:** `oracle/evidence/msl-machine/campaigns/erdos1084-harborth-2026-09-02/kernel/`
(`Erdos1084Lower.lean`, `.verify.json`, `.axioms.txt`, `.sha256`)
**sha256:** `eabb57f873d36bca83d24b3e7616fe053627179e8b82a05fff730820b97485ac`
**Verdict:** `lake env lean` → **exit 0**, **24.43 s**, Lean `v4.31.0-rc1` / Mathlib on the box.

### Axiom qualification (all twelve declarations)

```
'Erdos1084.le_f'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1084.dist_P_sq'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1084.unitDistNum_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1084.hex_lower'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1084.lower_k0' … 'lower_k6', 'lower_127'  — same three
```
**No `sorryAx`. No `Lean.ofReduceBool`** — i.e. `decide`, never `native_decide`; the kernel
did the arithmetic itself.

### What is proved

The three upstream definitions (`unitDistNum`, `Metric.IsSeparated'`, `Erdos1084.f`) are
reproduced **verbatim** in the file, so this is the target's `f`, not a paraphrase.

| declaration | statement |
|---|---|
| `le_f` | `#s = N → IsSeparated' 1 ↑s → unitDistNum s ≤ f d N` — the only place the `⨆` is unfolded. Boundedness (needed for `le_ciSup`; ℕ's `sSup` of an unbounded set is `0`) comes from the trivial pair count `#s.sym2 = (N+1).choose 2 ≤ N(N+1)`, no geometry. |
| `dist_P_sq` | **L0.** `dist (P p) (P q)^2 = ((u² + uv + v² : ℤ) : ℝ)` for `u = p₁−q₁, v = p₂−q₂`, where `P (a,b) = !₂[a + b/2, b·√3/2]`. This is the whole bridge from the real plane to integer arithmetic. |
| `unitDistNum_image` | **the transfer.** `unitDistNum (T.image P) = #{q ∈ T.sym2 \| qfS q = 1}` — the noncomputable `Sym2`/`Quot.out` unit-distance count equals a decidable integer count. Via `Finset.sym2_image`, injectivity of `Sym2.map P`, and `Sym2.lift`. |
| **`hex_lower`** | **general in k:** `∀ k, (idx k).card = 3k²+3k+1 → #{q ∈ (idx k).sym2 \| qfS q = 1} = 9k²+3k → 9k²+3k ≤ f 2 (3k²+3k+1)` |
| `lower_k0…k6` | the two hypotheses discharged by kernel `decide` at `k = 0,1,2,3,4,5,6` |

**The sealed numbers** (`n` pairwise-1-separated points in ℝ² realising that many unit distances):

| k | n = 3k²+3k+1 | 9k²+3k | sealed statement |
|---|---|---|---|
| 1 | 7 | 12 | `12 ≤ f 2 7` |
| 2 | 19 | 42 | `42 ≤ f 2 19` |
| 3 | 37 | 90 | `90 ≤ f 2 37` |
| 4 | 61 | 156 | `156 ≤ f 2 61` |
| 5 | 91 | 240 | `240 ≤ f 2 91` |
| 6 | 127 | 342 | `342 ≤ f 2 127` |

### The exact remaining obligation for symbolic k

`hex_lower` **is** the general theorem. Two purely combinatorial facts about a `Finset (ℤ × ℤ)`
are outstanding — **no geometry, no real numbers, no analysis is left in them**:

```lean
theorem idx_card    (k : ℕ) : (idx k).card = 3 * k ^ 2 + 3 * k + 1
theorem idx_unitnum (k : ℕ) : #{q ∈ (idx k).sym2 | qfS q = 1} = 9 * k ^ 2 + 3 * k
```

Routes (both verified numerically in `MINE/harborth_check.py`, k = 0…6):
- `idx_card`: fibrewise, `Finset.card_eq_sum_card_fiberwise` over the first coordinate — the
  fibre over `a` has `2k+1−|a|` elements, and `∑_{a=−k}^{k} (2k+1−|a|) = 3k²+3k+1`.
- `idx_unitnum`: induction on `k`. `idx (k+1) = idx k ∪ ring (k+1)`, `|ring m| = 6m`, and the
  added unit pairs are `6(k+1)` inside the ring plus `6 + 12k` spokes to ring `k`, total
  `18k+12`; then `9k²+3k + 18k+12 = 9(k+1)²+3(k+1)`. Equivalently by degree sum:
  `6·(3k²−3k+1) interior + 3·6 corners + 4·6(k−1) sides = 18k²+6k`, halved.

Estimated cost: **200–400 lines of `Finset` combinatorics over ℤ×ℤ.** No new Mathlib theory.

### One trap worth recording

`Finset.Icc (-(k:ℤ)) k` is **noncomputable** under `import Mathlib` in this toolchain — its
instance path resolves through `_root_.instConditionallyCompleteLinearOrder`, and every
`decide` below it dies. The index set is therefore built list-first
(`List.range … |>.flatMap … |>.filter … |>.toFinset`). This cost one compile round and is
documented in the file itself so the next session does not re-discover it.

---

## PART 3 — THE UPPER BOUND: SCOPE ONLY

### Mathlib has no planarity and no Euler formula for plane graphs — measured, not assumed

```
grep -rln "IsPlanar\|Planar" /root/mathlib4/Mathlib/
  → Mathlib/Combinatorics/SimpleGraph/Coloring/VertexColoring.lean   (a passing mention only)
grep -rn "eulerChar" /root/mathlib4/Mathlib/Combinatorics/
  → Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean   — the MÖBIUS Euler characteristic
    of a bounded poset, `mu 𝕜 ⊥ ⊤`.  Nothing to do with faces of a plane graph.
```

There is **no** `IsPlanar`, no combinatorial map, no face set, no `v − e + f = 2`.
Building it is a project in its own right (the referee's 1,500–2,500-line estimate is if
anything optimistic, since it needs an embedding theory Mathlib lacks entirely). **Do not.**

### Take the Euler-free route (route 2, angle-sum). Target: L2.

```lean
theorem L2 (S : Finset (ℝ^2)) (hsep : IsSeparated' 1 ↑S) (h3 : 3 ≤ S.card)
    (h : ℕ) (hh : h = #(S.filter (· ∈ frontier (convexHull ℝ ↑S)))) :
    unitDistNum S ≤ 3 * S.card - h - 3
```

The derivation, in the aggregate form (cleaner than per-vertex peeling, and it avoids the
degenerate cases the referee flagged in the `(-1,-1,+1)/(-1,-2,0)/(-1,-3,-1)` delta bookkeeping):

```
interior point v:            deg v ≤ 6                          (gaps ≥ 60° around 2π)
hull-boundary point v:       deg v ≤ 1 + 3·αᵥ/π                 (gaps ≥ 60° inside the cone αᵥ)
∑ over hull boundary of αᵥ = (h − 2)·π                           (convex polygon interior angles)
  ⇒ ∑_{hull} deg v ≤ h + 3(h − 2) = 4h − 6
  ⇒ 2e = ∑ deg ≤ 6(n − h) + (4h − 6) = 6n − 2h − 6
  ⇒ e ≤ 3n − h − 3.                                             ∎
```
Specialised at `n = 3k²+3k+1` with `h ≥ 6k` (obligation O7 below):
`e ≤ 3(3k²+3k+1) − 6k − 3 = 9k²+3k`. That closes `≤`, and with Part 2 closes the target.

### The obligation ladder — each rung a typed Lean statement

| # | Obligation | Lean statement (sketch) | Method | LOC |
|---|---|---|---|---|
| **O1** | **60° gap** | `dist x y = 1 → dist x z = 1 → 1 ≤ dist y z → y ≠ z → π/3 ≤ ∠ y x z` | `EuclideanGeometry.law_cos` (**exists**) gives `dist y z² = 2 − 2 cos θ ≥ 1 ⇒ cos θ ≤ 1/2`; then `Real.arccos` antitone + `nlinarith` | 40–80 |
| **O2** | **cyclic angular order + gap sum** | for a finite set of directions in ℝ², the consecutive angular gaps (in `Complex.arg` order) sum to `2π` | **NOT IN MATHLIB. THIS IS THE BLOCKER.** Sort a `Finset` of unit vectors by `Complex.arg`, prove the successor gaps telescope to `2π`, handle the wrap-around term | **300–600** |
| **O3** | interior degree ≤ 6 | `deg_G v ≤ 6` | O1 + O2: `6 · (π/3) = 2π` | 60–100 |
| **O4** | tangent cone at a hull point | if `v ∈ frontier (convexHull ℝ ↑S)` then `S \ {v}` lies in a closed cone at `v` of aperture `αᵥ ≤ π` | `geometric_hahn_banach_point_closed` (**exists**) for the supporting hyperplane; the cone/aperture packaging is new | 150–300 |
| **O5** | hull degree bound | `deg_G v ≤ 1 + ⌊3αᵥ/π⌋` for `v` on the hull | O1 + O2 + O4 (linear version of O3 inside a cone) | 100–150 |
| **O6** | convex polygon interior-angle sum | `∑_{v ∈ hull boundary} αᵥ = (h − 2) · π` | **NOT IN MATHLIB.** Induction on `h` via triangulation of a convex polygon, or the exterior-angle/winding form. Interacts with O2 (same cyclic-order machinery) | **400–800** |
| **O7** | packing ⇒ `h ≥ √(12n−3) − 3` | at `n = 3k²+3k+1`: `6k ≤ h` | perimeter `≥ h` (consecutive hull points are `≥ 1` apart) + area lower bound from the packing count. **No packing-density theory in Mathlib**; the *specialised* `h ≥ 6k` may be reachable more cheaply than the general isoperimetric form | **400–800** |
| **O8** | handshake | `∑ v, G.degree v = 2 * G.edgeFinset.card` | **`SimpleGraph.sum_degrees_eq_twice_card_edges` — EXISTS, free** | 0 |
| **O9** | `unitDistNum S = G.edgeFinset.card` | bridge the file's `Sym2`-filter count to a `SimpleGraph` | same shape as `unitDistNum_image`, already built once in Part 2 | 60–100 |
| **O10** | assemble | O3 + O5 + O6 + O8 ⇒ L2; + O7 ⇒ the specialisation | `linarith` / `omega` | 50–80 |

**Total: ~1,560–2,570 lines.**

### The honest read on route (2) vs Euler

Route (2) is **not dramatically cheaper in line count** than building Euler — the referee's
1,500–2,500 for Euler and my 1,560–2,570 for route (2) overlap. What makes route (2) the right
choice is different and, I think, decisive:

1. **Four of ten rungs are already free or nearly free** (O8 exists; O1 and O4 have their hard
   analytic cores in Mathlib already — `law_cos`, `geometric_hahn_banach_point_closed`; O9 was
   built tonight).
2. **Every rung is a standalone, reusable Euclidean-geometry statement.** O2 and O6 in
   particular are things Mathlib *should* have and would take on. The Euler route produces one
   monolithic embedding theory usable for nothing else until it is complete.
3. **It fails loudly.** Each rung is independently checkable; a wrong constant shows up at that
   rung rather than three layers down inside a face-counting argument.

**The single decisive missing primitive is O2** — the cyclic angular order and its gap sum.
Everything geometric in the ladder (O3, O5, and half of O6) is downstream of it. If one thing
gets built next on this problem, build O2; it is self-contained, has no dependency on the rest
of the ladder, and is the thing nothing in Mathlib provides.

**Caveat on the per-vertex peel (route 1).** I did not take it, and I flag why: the claim "a
hull vertex has unit-degree ≤ 3" needs a *strictly* supporting line. With a merely closed
supporting half-plane the cone aperture can be exactly `π`, which admits **4** neighbours
(`3 × 60° = 180°`), not 3. The aggregate form (O6) sidesteps this entirely because
`∑ αᵥ = (h−2)π` already charges the deficiency globally. Anyone attempting route (1) should
budget for that case split explicitly.

---

## What closing this variant would mean — one honest line

**It would be a known 1974 theorem formalized, not a research-open problem solved** — but it
would be the first machine-checked proof of any part of Harborth's bound, and the run itself
produced a second, separately citable finding: **the DeepMind corpus has this variant
mis-tagged `research open` when it was settled in 1974**, which is exactly the kind of error a
formalization pass exists to catch and is worth sending upstream on its own.

---

## Files

| what | where |
|---|---|
| sealed Lean | `oracle/evidence/msl-machine/campaigns/erdos1084-harborth-2026-09-02/kernel/Erdos1084Lower.lean` |
| kernel verdict | `…/kernel/Erdos1084Lower.verify.json` |
| axioms | `…/kernel/Erdos1084Lower.axioms.txt` |
| hash | `…/kernel/Erdos1084Lower.sha256` |
| prior-art corpus + mission | `…/prior-art/nf-corpus-1084.json`, `nf-mission-1084.json` |
| working copy + probes | `MINE/e1084/` |
| the scan that found it | `MINE/pool-wang-top.json` (row 1), `MINE/harborth_check.py` |

**Reproduce:**
```bash
scp Erdos1084Lower.lean root@51.15.107.148:/root/peer/e1084/
ssh root@51.15.107.148 'cd /root/mathlib4 && export PATH=/root/.elan/bin:$PATH && \
  lake env lean /root/peer/e1084/Erdos1084Lower.lean'   # exit 0, ~25 s
```

**Spend this session: USD 0.00.** No proposer calls were made — the target was decidable
deterministically, so the budget was never opened.
