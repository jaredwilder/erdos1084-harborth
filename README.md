# erdos1084-harborth

Work on `erdos_1084.variants.triangular_optimal_d2`, plus a **correction to the prior-art tag**
carried by that statement in DeepMind's formal-conjectures repository.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## The correction, which is the useful part

The statement

    f 2 (3k^2 + 3k + 1) = 9k^2 + 3k

is tagged `@[category research open]` in `FormalConjectures/ErdosProblems/1084.lean`.

**It is not open.** It follows from Heiko Harborth, *Lösung zu Problem 664A*, Elemente der
Mathematik 29 (1974), 14-15, which proves a penny graph on n vertices has at most
`floor(3n - sqrt(12n - 3))` edges and that the bound is sharp, attained by a hexagonal piece of
the triangular lattice. A penny graph is exactly the object in the Lean file: points pairwise at
distance at least 1, edges the pairs at distance exactly 1. Harborth's e(n) is f 2 n verbatim.

The floor bound gives equality precisely at n = 3k^2 + 3k + 1, because there 12n - 3 = (6k + 3)^2
is a perfect square. `REPORT-2026-09-02.md` carries the algebra and a numerical check to k <= 59.

If you maintain formal-conjectures, this row's category tag is wrong and the citation above is
the fix.

## The formalization work

- `kernel/` - the lower bound, **kernel-sealed for k = 0..6**, 12 declarations, clean axiom
  footprint, no `native_decide`. The general-k theorem `hex_lower` is proved for symbolic k;
  only its two finite integer counts are per-k.
- `upper/` - 69 Lean files attacking the upper bound. **52 are sorry-free.** The remaining 16
  each name one explicit gap. This covers the arithmetic and angular half of the argument.
- `prior-art/` - the novelty-search corpus and mission files behind the Harborth identification.

## What is not claimed

The upper bound is not closed here. The two walls are named in the report rather than papered
over: Mathlib appears to lack the planar Steiner formula and the isoperimetric inequality for
convex bodies, and it has no "convex polygon in cyclic order" predicate.

## License

Apache-2.0.
