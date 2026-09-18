# Erdős #1084 — Harborth's penny-graph theorem in Lean

For

\[
n=3k^2+3k+1,
\]

the two-dimensional extremal function in Erdős #1084 satisfies

\[
\boxed{f_2(n)=9k^2+3k}.
\]

This special case is classical: it follows directly from Heiko Harborth's 1974 sharp edge bound for penny graphs. The repository records the short derivation and develops the corresponding Lean formalization.

## Harborth's theorem

Harborth proved that a penny graph on `n` vertices has at most

\[
\left\lfloor 3n-\sqrt{12n-3}\right\rfloor
\]

edges, with equality attained by suitable hexagonal pieces of the triangular lattice.

The geometric object used in Erdős #1084 is exactly a penny graph: the points are pairwise at distance at least one, and an edge joins two points precisely when their distance is one.

At

\[
n=3k^2+3k+1,
\]

we have

\[
12n-3=(6k+3)^2.
\]

Therefore Harborth's formula gives

\[
3(3k^2+3k+1)-(6k+3)=9k^2+3k,
\]

which is the displayed equality.

The algebra and a numerical check through `k<=59` are recorded in [`REPORT-2026-09-02.md`](REPORT-2026-09-02.md).

## Formalization

The Lean development has two layers.

### Lower bound

`kernel/` contains the constructive lower-bound development, including the symbolic theorem `hex_lower`. The recorded package has **12 declarations with clean axiom footprints**, no `sorry`, and no `native_decide`.

### Upper bound

`upper/` contains **69 Lean files** developing Harborth's upper-bound argument. Of these, **52 are sorry-free**. The remaining files isolate the geometric infrastructure still missing from the formal proof.

The principal unresolved formalization ingredients are:

- planar Steiner-formula / isoperimetric machinery for convex bodies;
- a convenient Mathlib representation of convex polygons in cyclic order.

These are formalization gaps, not gaps in Harborth's 1974 theorem.

## FormalConjectures correction

The variant

```text
f 2 (3k^2 + 3k + 1) = 9k^2 + 3k
```

was recorded as research-open in `FormalConjectures/ErdosProblems/1084.lean`. The Harborth theorem above supplies the classical reference for that statement, so the corresponding problem metadata should cite Harborth rather than present the variant as open.

## Reference

Heiko Harborth, *Lösung zu Problem 664A*, **Elemente der Mathematik** 29 (1974), 14–15.

## Repository map

- `kernel/` — constructive lower bound and symbolic general-`k` theorem;
- `upper/` — formalization of the sharp upper-bound argument;
- `prior-art/` — source and literature notes;
- `REPORT-2026-09-02.md` — derivation and numerical checks.

Author: Jared Wilder. License: Apache-2.0.
