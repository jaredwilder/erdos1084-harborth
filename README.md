# Erdős 1084: Harborth's 1974 theorem and Lean formalization

This repository records a correction to the open-problem metadata for `erdos_1084.variants.triangular_optimal_d2` and formalization work around the corresponding extremal penny-graph bound.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Prior-art correction

The statement

```text
f 2 (3k^2 + 3k + 1) = 9k^2 + 3k
```

is tagged `@[category research open]` in `FormalConjectures/ErdosProblems/1084.lean`.

That special case follows from Heiko Harborth, *Lösung zu Problem 664A*, *Elemente der Mathematik* 29 (1974), 14–15. Harborth proves that a penny graph on `n` vertices has at most

```text
floor(3n - sqrt(12n - 3))
```

edges and that the bound is sharp, attained by hexagonal pieces of the triangular lattice.

The geometric object in the Lean file is exactly a penny graph: points are pairwise at distance at least 1 and edges join pairs at distance exactly 1. Harborth's `e(n)` therefore matches `f 2 n`.

At `n = 3k^2 + 3k + 1`,

```text
12n - 3 = (6k + 3)^2,
```

so the floor bound gives the displayed equality. `REPORT-2026-09-02.md` contains the algebra and a numerical check through `k <= 59`.

The practical correction for formal-conjectures is therefore to replace the research-open tag on this variant with the Harborth citation.

## Lean formalization

- `kernel/` — lower-bound development, including a symbolic general-`k` theorem `hex_lower`; 12 declarations with clean axiom footprints and no `native_decide`.
- `upper/` — 69 Lean files formalizing the upper-bound argument; **52 are sorry-free** and the remaining files isolate the missing geometric ingredients explicitly.
- `prior-art/` — literature-search notes and source material documenting the Harborth identification.

## Remaining formalization work

The unresolved Lean work is in the geometric upper-bound infrastructure rather than the special-case mathematics itself. The current missing ingredients are planar Steiner-formula/isoperimetric machinery for convex bodies and a convenient Mathlib representation of a convex polygon in cyclic order.

Those gaps are formalization dependencies; the Harborth theorem and its implication for the displayed special case are classical mathematics from 1974.

## License

Apache-2.0.