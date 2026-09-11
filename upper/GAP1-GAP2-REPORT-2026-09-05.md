# GAP 1 AND GAP 2 CLOSED — THE FAN BRANCH NOW RUNS ON POLAR DATA ALONE

**Session:** erdos:1084 upper ladder, 2026-09-05 evening, continuing
`S1-REPORT-2026-09-05.md` (S1 closed, H3 assembled, `e1084_hull_angle_sum` spliced).
**Kernel:** every run on `root@51.158.234.15`, project `/root/formalizer/proofs`,
Mathlib `919544d430`, toolchain `leanprover/lean4:v4.31.0-rc1`, `lake env lean`
**exit 0**, `nice -n 19`, box load ~31–33 on 32 cores, no existing job touched.
Zero `sorry`; clean axiom triple `{propext, Classical.choice, Quot.sound}` on **every**
declaration below. **No local compile.** All four files were re-run from scratch after the
last edit (`receipts-box-2026-09-05-gap1/VERIFY-RERUN.txt`, with md5 of the compiled bytes).

---

## 1. WHAT WAS SEALED

| node | theorem(s) | file | receipt |
|---|---|---|---|
| `G1A` | `extremePoint_mem_frontier`, `vertexPts_subset_hullPts`, `convexHull_subset_hullPts` | `H3G_Frontier.lean` | `H3G_Frontier.axioms.txt` |
| `G1B` | `s2_sides_to_polar_ge`, `s1_frontier_signs`, `h3_frontier_inside` | `H3G_Frontier.lean` | same |
| `G1X` | `e1084_frontier_angle_sum`, `e1084_hullPts_angle_sum` | `H3G_Frontier.lean` | same |
| `G1M` | `e1084_flat_model`, `flat_cross_zero`, `flat_angle_pi` | `H3G_FlatModel.lean` | `H3G_FlatModel.axioms.txt` |
| `G2` | `gap_lt_pi`, `gap_lt_pi_hullPts` | `G2_GapCeiling.lean` | `G2_GapCeiling.axioms.txt` |
| `H05` | `hull_angle_package_pre` (re-verified verbatim; **had no DAG node until now**) | `H05G_Assembly.lean` | `H05G_Assembly.axioms.txt` |
| `H05F` | `fanInterface_of_polarFan`, `hull_angle_package_of_polar` | `H05G_Assembly.lean` | same |

DAG after this session: **45 nodes, 23 `PROVED_KERNEL`, 2 `REFUTED`, 19 open**
(was 38 / 16 / 2 / 19). Backup of the previous DAG: `gap1-2026-09-05/erdos1084.upper.dag.json.bak`.

**The headline is `hull_angle_package_of_polar`.** `H05_Assembly.lean` proved the package
from `FanInterface S h` — an interface that **assumed** the interior-angle sum. That
assumption is gone. The fan branch now takes a closed polar listing of `hullPts` about an
interior centre, plus the per-vertex packing bound, and nothing else.

---

## 2. GAP 1a — THE CHEAP DIRECTION WAS CHEAPER THAN THE MAP SAID

The API map (`HULL-ANGLE-API-MAP-2026-09-05.md`, Risk 1) routed `vertexPts ⊆ hullPts`
through the separating functional. It needs no separation at all:

> An interior point of `A` has a ball around it, so it is the **midpoint of two distinct
> points of `A`** — which extremality forbids. Being in `A` it is in the closure, and
> `frontier = closure \ interior`.

Eleven lines. Mathlib's own TODO (`Analysis/Convex/Extreme.lean:40`) is closed **in the
direction the campaign needs**; the converse is false and is not claimed.

The same lemma then buys the covering that gap 2 needs. Krein–Milman
(`closure_convexHull_extremePoints`) plus "the hull of a finite set is compact" plus "the
hull of the finite extreme set is closed" gives

```
convexHull ℝ S = convexHull ℝ (extremePoints) ⊆ convexHull ℝ (hullPts S)
```

⛔ **This is why gap 1a had to land before gap 2, not after.**

---

## 3. GAP 1b — THE DEGENERATE BRANCH, AND A SIMPLER PROOF THAN THE ONE IT REPLACES

`s1_consecutive_signs` concluded `0 < cross (p (i+1)) (p i) (p (i+2))`. At three collinear
listed points that is **false**, which is exactly why `H3X` could not index `hullPts`. The
repair is not a patch on the old route — it is a **weaker conclusion with a weaker
hypothesis**, and the proof got shorter:

| | sealed extreme route (`H3_Assembled`) | frontier route (this file) |
|---|---|---|
| listed points | `p i ∈ A.extremePoints ℝ` | `p i ∈ A`, `p i ∉ interior A` |
| centre | `v₀ ∈ A` | `v₀ ∈ interior A` |
| turn | `0 < cross` | `0 ≤ cross` |
| contradiction | extreme point in an open segment | interior point where none is allowed |
| non-degeneracies needed | `p(i+1) ≠ v₀`, `p(i+1) ≠ p i` | **none** |

The mechanism: a **strictly** right turn makes Cramer's weights satisfy `λ + μ < 1`
strictly, so `p (i+1)` sits on the **open segment** from the interior point `v₀` to a point
of `A`, hence in `interior A` (`Convex.openSegment_interior_self_subset_interior`) —
forbidden for a frontier point. A **straight** turn is now admitted.

S2 was generalized in the same move. The two cross-product PRODUCTS the frozen socket
carried were only ever transport for two signs; stated directly as
`0 < cross Y X v` and `0 < cross Y v Z`, the orientation relaxes to `0 ≤ cross Y X Z`. At
equality `sin (γ − α) = 0` with `γ − α ∈ (0, 2π)`, so `γ − α = π` exactly — the flat vertex,
interior angle `π`, and `InsideAngleAt` still holds. **Both sides of the socket moved
together, and the model below checks that they still meet.**

---

## 4. THE DEGENERATE MODEL — NON-VACUITY IS A RECEIPT, TWICE OVER

Campaign law, from the file that caught the ascending/descending defect: *a socket offered
UNMODELLED is how a false statement survives.* `e1084_frontier_angle_sum` claims something
`e1084_hull_angle_sum` cannot, so a listing of exactly that kind was built and run:

```
   (-1,1) ---- (0,1) ---- (1,1)      <- three COLLINEAR listed points
      |                      |
      |          0           |       <- v0, interior to the strip |y| <= 1
      |                      |
   (-1,-1) ------------ (1,-1)
```

Five listed points at polar angles `π/2, π/4, −π/4, −3π/4, −5π/4`; gaps
`π/4, π/2, π/2, π/2, π/4` summing to `2π`; `h = 5`; the theorem returns **`3π`**.

Two further theorems make the degeneracy load-bearing rather than decorative:

* **`flat_cross_zero`** — `cross (qq 5) (qq 4) (qq 6) = 0`. The strict cross product
  concluded by the sealed extreme-point route is **FALSE** here. This configuration is
  provably outside `s1_consecutive_signs`, so the new statement is not a re-packaging of the
  old one.
* **`flat_angle_pi`** — the flat vertex carries interior angle **exactly `π`**.

The strip was chosen because its interior is provable in a dozen lines (`|y| ≤ ‖x‖`, plus a
push in the normal direction), which sidesteps computing the interior of a polytope.

---

## 5. GAP 2 — THE STRICT GAP CEILING IS NOW A THEOREM

`S1-REPORT-2026-09-05.md` §5 declared `hlt : ∀ i, a i − a (i+1) < π` **UNPROVED**. It is
proved (`gap_lt_pi`), by the argument the report sketched, made precise:

If a gap reached `π`, then — gaps being positive and summing to `2π` over one period — every
listed point has polar angle in `[a(k+1) − π, a(k+1)]`, so the functional
`x ↦ ⟨x − v₀, n⟩` at `n = a(k+1) + π/2` evaluates to `r_j · sin(θ_j − a(k+1)) ≤ 0` at every
listed point. That half-plane is convex, hence contains the hull of the listing, hence (by
the covering) `A`. But `v₀` is **on its bounding line**, so no ball around `v₀` fits in `A`.
Contradiction with `v₀ ∈ interior A`.

⛔ **THE COVERING IS NOT A NEW ASSUMPTION.** `gap_lt_pi_hullPts` discharges it from gap 1a
plus the **surjectivity onto `hullPts` that `FanInterface` already demanded**. The consumer
supplies nothing it was not already supplying.

What the proof does **not** need: no supporting-hyperplane API, no separation theorem, no
Mathlib frontier characterisation. What it does need: the argument function is `2π`-periodic
across the period (`hpera`), which any closed listing carries.

---

## 6. THE ASSEMBLY — WHAT `FanInterface` NOW COSTS

`fanInterface_of_polarFan` produces H05's interface from `PolarFan S h`:

| `FanInterface` clause | discharged by |
|---|---|
| listed points in `hullPts`, injective, surjective | the listing (hypothesis) |
| `Σ` interior angles `= (h−2)π` | **`e1084_hullPts_angle_sum`** (G1X) |
| the angle split at each vertex | **`h3_frontier_inside`** (G1B) |
| the central total `2π` | **`hcentral_of_polar_desc`** + `gap_sum_of_period` (telescoping) |
| the strict gap ceiling `< π`, at EVERY index | **`gap_lt_pi_hullPts`** (G2) + `gap_periodic` |
| the covering | **`convexHull_subset_hullPts`** (G1A) |
| the per-vertex packing bound | **still a hypothesis** |

Note the index arithmetic: gap 2 gives the ceiling for `k < h`; `gap_periodic` lifts it to
every `k : ℕ` (the gaps are `h`-periodic because `a (i+h) = a i − 2π`), which is what the
splice, whose hypotheses range over all of `ℕ`, actually consumes.

---

## 7. WHAT REMAINS — AT ITS TRUE STRENGTH

⛔ **TWO INPUTS OF `PolarFan` ARE OPEN AND ARE NOT CLAIMED.**

1. **THE CONSTRUCTION OF THE LISTING.** That the frontier points of `S` admit an
   `h`-periodic, strictly descending, injective-and-surjective polar listing about *some*
   interior `v₀` — θ-injectivity of hull points seen from an interior point, Risk 3 of the
   API map. `PolarFan` takes it as given. **This is now the single largest open obligation
   under the fan branch.**
2. **THE PER-VERTEX PACKING BOUND** `udeg ≤ 1 + 3α/π` at the listed aperture. H04's
   `h4_cone_packing` is sealed; its **instantiation** at the listed angle is not.

Unchanged and still open above this rung: `hcentral` at `m ≤ 3` (Contract C §3) for the
other route, and everything outside the hull-angle package.

⛔ **WHAT THIS SESSION DID NOT PROVE:** that a suitable `v₀` exists (the listing hypothesis
presupposes an interior point — for a degenerate `S` with empty hull interior there is none,
and that case is not treated here); and nothing about the *lower* bound or the final
`u(n)` statement. The upper bound is **not** closed.

⛔ **TWO EXISTING DAG NODES WERE EDITED, NOT ONLY APPENDED.** `H3S1`'s residue ("the gap
ceiling ... is DECLARED UNPROVED") and `H3X`'s residue ("BOTH ARE OPEN") were prefixed with
a dated `CLOSED 2026-09-05 by ...` line naming the closing node; the original text is
preserved verbatim after it. Nothing was deleted.

---

## 8. FILES

```
upper/H3G_Frontier.lean       gap 1a + gap 1b + the frontier splice + the ball model
upper/G2_GapCeiling.lean      gap 2, self-contained
upper/H05G_Assembly.lean      H05 verbatim + FanInterface produced from polar data
upper/H3G_FlatModel.lean      the DEGENERATE model (flat vertex), self-contained
upper/receipts-box-2026-09-05-gap1/
    BACKEND.txt               box, Mathlib rev, toolchain, per-file exit codes
    VERIFY-RERUN.txt          clean re-run of all four + md5 of the compiled bytes
    <file>.axioms.txt         the axiom prints
    <file>.log                full compiler logs (warnings only)
upper/gap1-2026-09-05/        working copies, probeA.lean, the DAG-append script, DAG backup
```

Every file is self-contained (`import Mathlib`, its own copy of every verbatim definition,
no shared module) exactly as `RUN-ON-BOX.sh` requires. `H05G_Assembly.lean` and
`H3G_FlatModel.lean` therefore each carry a full copy of the `H3G_Frontier` chain, and
re-verify it.
