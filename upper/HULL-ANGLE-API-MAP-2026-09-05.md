# HULL-ANGLE API MAP — pinned Mathlib 919544d4 / v4.31.0-rc1 (recon agent, 2026-09-05)

> Probe-verified: every row below was `#check`-compiled or grep-confirmed on the box.
> Probe sources + logs: `hullrecon-2026-09-05/` (this dir). Serves the H-rung development
> (H00_HullAngle_SCAFFOLD.lean) and Contract C's InsideAngleAt consumer end.

## THE THREE HEADLINES

1. **`Mathlib/Geometry/Polygon/Basic.lean` EXISTS** (new 2026): `Polygon P n` with
   `vertices : Fin n → P`, `HasNondegenerateEdges/Vertices`, `edgePath`, `edgeSet`,
   `boundary`, Triangle↪Polygon 3. NO convexity, NO angles, NO angle sum, NO simplicity.
   Recommendation: stay ℕ-indexed on `Finset.range h` (no instance burden — verified);
   convert to `Polygon` only for upstreaming. `finRotate_succ_apply` deprecated →
   `finRotate_apply : (finRotate n) i = i + 1`. `Fin h` arithmetic needs `[NeZero h]`.
2. **NO unoriented angle additivity exists anywhere** (all 66 decls of
   Angle/Unoriented/Affine.lean enumerated): no `∠ a v d + ∠ d v b = ∠ a v b` under any
   hypothesis. Every cone/fan argument MUST run oriented (`oangle_add`, free) and convert
   at the end via `angle_eq_abs_oangle_toReal` — sign-constancy is what lets |·|
   distribute over sums; without it the conversion is FALSE.
3. **The supporting line is 4 lines, compiled** (probe3, clean): `geometric_hahn_banach_open_point`
   applied to `interior (convexHull ℝ ↑S)` + `hv.2` from frontier membership. Mathlib has
   no "supporting hyperplane" by name; this IS it. (Old path
   `Analysis/NormedSpace/HahnBanach/Separation.lean` is a deprecated shim; live home is
   `Analysis/LocallyConvex/Separation.lean`.)

## INSTANCES — both missing globally, both fixes compiled clean

```lean
instance factFinrank2 : Fact (Module.finrank ℝ (ℝ^ 2) = 2) := ⟨finrank_euclideanSpace_fin⟩
instance orientedPlane : Module.Oriented ℝ (ℝ^ 2) (Fin 2) :=
  ⟨((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).orientation⟩
```
⚠️ `Basis.orientation` is NOT a name on this rev — it is `Module.Basis.orientation`
(protected; dot notation resolves, fully-qualified `Basis.orientation` errors).
⚠️ `EuclideanGeometry.oangle` (`∡`) needs `Module.Oriented`, not just `Fact` — this is why
O05 stayed at the vector layer. ⚠️ Finset.filter over frontier/extremePoints membership
needs `open scoped Classical`.

## KEY NAMES (all probe-confirmed on this rev)

**Triangle/unoriented:** `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` (ONLY
hypothesis `p₂ ≠ p₁`; both degenerate instantiations compile — no non-collinearity needed)
· `angle_nonneg/angle_le_pi/angle_comm/law_cos` · `angle_add_angle_eq_pi_of_angle_eq_pi` ·
`angle_self_of_ne` (⚠️ `angle_self` does NOT exist) · `angle_eq_pi_iff_sbtw` ·
`Sbtw.angle_eq_right` / `Wbtw.angle_eq_left` · `exterior_angle_eq_angle_add_angle` ·
`angle_lt_pi_of_not_collinear` / `angle_pos_of_not_collinear`.

**Oriented (affine layer, `∡` — prefer it):** `EuclideanGeometry.oangle_add`
(`p₁≠p → p₂≠p → p₃≠p → ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃`) · `oangle_sub_left/right` ·
`oangle_add_cyc3` · `oangle_rev` (unconditional) · `angle_eq_abs_oangle_toReal` ·
`oangle_eq_zero_or_eq_pi_iff_collinear` · `oangle_ne_zero_and_ne_pi_iff_affineIndependent` ·
`oangle_eq_pi_iff_sbtw` / `oangle_eq_zero_iff_wbtw` · **`AffineSubspace.SSameSide.oangle_sign_eq`**
(Affine.lean:808 — all points strictly one side of a line see a segment with one
orientation sign = "the cone at a hull vertex lies in a half-plane" in oriented form; dual
`SOppSide.oangle_sign_eq_neg`).

**Vector layer:** `Orientation.oangle/oangle_add/oangle_rev/angle_eq_abs_oangle_toReal/
oangle_eq_zero_iff_sameRay/oangle_smul_left_of_pos/rotation/oangle_map` + ~30
`oangle_sign_*` (Basic.lean:745-880).

**Real.Angle:** `toReal` · `neg_pi_lt_toReal` · `toReal_le_pi` · `abs_toReal_le_pi` ·
`toReal_coe_eq_self_iff` · `coe_toReal` · `coe_sub/add/nsmul/zsmul` · `toReal_injective` ·
`sign` · `sign_eq_zero_iff` · `angle_eq_iff_two_pi_dvd_sub`. Real.Angle is an
AddCommGroup — `Finset.sum` + `Finset.sum_range_sub` telescope WORK in it (compiled).
Real.Angle has `CircularOrder`, NO `LinearOrder` (#synth failed).

**Convex hull:** `Set.Finite.isCompact_convexHull` (𝕜 explicit) / `isClosed_convexHull` ·
`Finset.convexHull_eq` · `convexHull_eq_union` (Carathéodory) · `Set.extremePoints` /
`mem_extremePoints` · `extremePoints_subset` (ROOT namespace) ·
`extremePoints_convexHull_subset` (vertices ⊆ S) ·
`Convex.mem_extremePoints_iff_mem_diff_convexHull_diff` / `_iff_convex_diff` ·
`IsCompact.extremePoints_nonempty` (Krein–Milman) · `closure_convexHull_extremePoints`
(finite case: convexHull(vertices) = hull, closure redundant) · `IsExposed` /
`IsExposed.eq_inter_halfSpace` · `exposedPoints_subset_extremePoints` ·
`ConvexIndependent` (= convex position) · `Convex.convexIndependent_extremePoints` ·
`IsVisible` / `IsClosed.exists_wbtw_isVisible` · `geometric_hahn_banach_open_point` ·
`Convex.interior_nonempty_iff_affineSpan_eq_top` (the non-degeneracy gate) ·
`AffineSubspace.SSameSide/WSameSide/SOppSide` · `intrinsicFrontier` /
`intrinsicClosure_eq_closure` (finite dim).

**Sorting:** `Finset.orderIsoOfFin` / `orderEmbOfFin` / `orderEmbOfFin_mem` /
`range_orderEmbOfFin` — ALL need `[LinearOrder]`. `monoEquivOfFin` is root-namespace.
NO Finset layer over circular orders; NO sortBy/sortCircular (probed absent).
`Finset.sort` with a key-relation fails Std.Antisymm for non-injective keys.

## THE FIVE RISKS (nothing exists; cheapest routes)

1. **extremePoints ↔ frontier NEVER MEET** — Mathlib's own TODO (Extreme.lean:40,
   Exposed.lean:41). Route: prove ONLY `vertexPts ⊆ hullPts` (extreme point ∉ interior via
   the separating functional); KEEP `hullPts` as the index set — a non-extreme frontier
   point contributes angle exactly π to the sum, so (h−2)π stays TRUE over all frontier
   points. Feature, not compromise; O05's h untouched.
2. **No interior-angle definition** — define `α v := ∠ (prev v) v (next v)` from a
   constructed cyclic enumeration; carry proofs in the `∡`-based `(∡ … ).toReal` form
   (additive), convert to `∠` last. NEVER an inf/sup-over-cone definition (no support,
   every step re-derives).
3. **No cyclic sorting** — cut the circle at an interior point c: `θ v := (∡ e c v).toReal
   ∈ (−π, π]` exactly as `o02_argument_function` builds it; sort real values via
   `orderEmbOfFin`. **θ-injectivity on hull points from interior c is LOAD-BEARING —
   prove it, never assume it** (two hull points at one argument from an interior point
   force c outside the hull). This is where a "true theorem about nothing" would enter.
4. **No unoriented additivity** — see headline 2. `abs_toReal_coe_le` +
   `o02_argument_function` (both sealed, clean triple, in O05_DegreeSumBound.lean) are
   the Risk-4 primitives, reusable verbatim.
5. **No polygon angle sum** — build ℕ-indexed, fan-induct from p 0 with
   `angle_add_angle_add_angle_eq_pi` (base case hypothesis-free — verified), splits via
   `oangle_add`. Fallback: the turning-angle form `Σ(π − ∠…) = 2π` telescopes in
   Real.Angle via `Finset.sum_range_sub` (one line; ℝ-version already sealed as O02e).
