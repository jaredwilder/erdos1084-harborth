import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-!
# erdos:1084 upper -- O07 STATEMENT DEFECT, kernel-exhibited

`o07_hull_size_lower_bound` as frozen in `O07_HullSizeLowerBound_SCAFFOLD.lean` is **FALSE**,
and it is false for **every** `k ≥ 1`, by an **unbounded** margin.

    FROZEN:  1-separated `S` with `#S = 3k²+3k+1`  ⇒  `6k ≤ #(hullPts S)`.
    TRUTH:   for every `k ≥ 1` there is such an `S` with `#(hullPts S) ≤ 3`.

WITNESS (all lattice points, so 1-separation is free):  three corners of a LARGE triangle,
`(0,0)`, `(m+2,0)`, `(0,m+2)`, together with the interior row `(1,1), (2,1), …, (m,1)`,
at `m = 3k²+3k-2`.  Every row point sits at distance `≥ 1/2` from all three edges of the
triangle, hence in the **interior** of the hull, hence NOT on its frontier.  Only the three
corners can survive in `hullPts`, so `#(hullPts S) ≤ 3 < 6k`.

⛔ WHY THE SCAFFOLD'S OWN ROUTE COULD NOT HAVE WORKED, AND WHY THIS IS NOT A NEAR MISS.
The scaffold proposed: disjoint discs of radius `1/2` inside `hull ⊕ B(0,1/2)`, Steiner
`A + P/2 + π/4`, isoperimetry `4πA ≤ P²`, and `P ≥ h` because consecutive hull points are
`≥ 1` apart.  Grant every one of those, including the two theories Mathlib lacks.  The
packing inequality then yields a **LOWER** bound on the perimeter, `P ≥ π(√n − 1)`, while
`P ≥ h` bounds `h` from **ABOVE**.  The two never compose into a lower bound on `h`.  The
missing Steiner formula and the missing isoperimetric inequality were never the obstruction:
**the inequality chain points the wrong way**, and no amount of Mathlib would fix it.

⛔ WHAT THE DEFECT ACTUALLY IS — AND WHY IT IS IN O07 AND NOT IN O05.  Harborth's `h` is
NOT the number of points of `S` on the frontier of `convexHull S`.  It is the number of
vertices on the **outer face of the planar drawing of the unit-distance (penny) graph**.
Write `b` for that count.  Always `#(hullPts S) ≤ b`, because every point on the hull
frontier lies on the outer face.  The two rungs use `h` with OPPOSITE polarity:

  * O05 concludes `e ≤ 3n − h − 3`, which is WEAKENED by a smaller `h`.  Substituting the
    hull count for `b` is therefore SOUND there — it is a valid lower bound for `b`, and
    O05 keeps its meaning (it merely stops being sharp).
  * O07 must produce `h ≥ 6k`, a LOWER bound.  Here the substitution is invalid in the
    only direction that matters, and the theorem below shows it fails catastrophically:
    the hull count is not bounded below by ANY function of `n` (`hull_count_has_no_lower_bound`).

The two counts agree for the hexagonal patch — which is why the target value `6k` is the
right one — and they diverge without bound as soon as the unit-distance graph is not
connected, or the hull is not tight around it.  In the witness above `b = m + 3 = 3k²+3k+1`
(the graph is a path on the row plus three isolated corners, so every vertex is on the outer
face) while `#(hullPts S) = 3`.

REPAIR DIRECTION (not proved here; this is a RESEARCH-SIZED task, not a rewrite): O07 must
be restated with `b`, the outer-face vertex count of the unit-distance graph, and O05 must
be restated with the same `b` (its hull form stays true but is then too weak to feed O10).
Mathlib has no planar-face API, so `b` has to be built before the rung can even be stated.
⛔ Do NOT "repair" O07 by replacing the frontier of the hull with the frontier of the union
of the closed discs of radius `1/2`: 1-separation makes those discs pairwise
interior-disjoint, so EVERY point of `S` would qualify and the count would collapse to `n`,
which is a true but useless `≥ 6k` that then breaks O05 instead.

The verbatim preamble is reproduced from the scaffold: `Metric.IsSeparated'`, the `ℝ^ n`
notation, and `Erdos1084Upper.hullPts` (under the same `open scoped Classical`), so the
proposition refuted below is the frozen one, not a paraphrase.

STATUS: REFUTATION, kernel-exhibited.  The `sorry` in the scaffold is UNDISCHARGEABLE.
-/

open scoped ENNReal

/-- (VERBATIM: FormalConjecturesForMathlib/Geometry/Euclidean.lean) -/
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-- A set `s` is `≥ eps`-separated if its elements are pairwise at distance greater or
equal to `eps` from each other.
(VERBATIM: FormalConjecturesForMathlib/Topology/MetricSpace/MetricSeparated.lean) -/
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)

end Metric

/-! ## Part 0 -- the integer configuration.

Stated BEFORE `open scoped Classical`, so the `DecidableEq (ℤ × ℤ)` instance in `insert`
stays the computable one (the campaign's recorded trap: a noncomputable instance in scope
kills the decision procedures under a `Finset` literal). -/

namespace O07Refute

/-- The interior row `(1,1), (2,1), …, (m,1)`. -/
def row (m : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range m).image (fun i : ℕ => ((i : ℤ) + 1, (1 : ℤ)))

/-- The witness configuration: three corners of a large triangle, and the row inside it. -/
def cfg (m : ℕ) : Finset (ℤ × ℤ) :=
  insert ((0 : ℤ), (0 : ℤ))
    (insert (((m : ℤ) + 2), (0 : ℤ))
      (insert ((0 : ℤ), ((m : ℤ) + 2)) (row m)))

theorem rowf_inj : Function.Injective (fun i : ℕ => ((i : ℤ) + 1, (1 : ℤ))) := by
  intro i j h
  have h1 : (i : ℤ) + 1 = (j : ℤ) + 1 := congrArg Prod.fst h
  omega

theorem row_card (m : ℕ) : (row m).card = m := by
  rw [row, Finset.card_image_of_injective _ rowf_inj, Finset.card_range]

theorem mem_row (m : ℕ) (p : ℤ × ℤ) (hp : p ∈ row m) :
    p.2 = 1 ∧ 1 ≤ p.1 ∧ p.1 ≤ (m : ℤ) := by
  rw [row, Finset.mem_image] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hi' : i < m := Finset.mem_range.mp hi
  dsimp only
  exact ⟨rfl, by omega, by omega⟩

theorem corner1_not_row (m : ℕ) : ((0 : ℤ), (0 : ℤ)) ∉ row m := by
  intro h
  have h1 := (mem_row m _ h).1
  dsimp only at h1
  omega

theorem corner2_not_row (m : ℕ) : (((m : ℤ) + 2), (0 : ℤ)) ∉ row m := by
  intro h
  have h1 := (mem_row m _ h).1
  dsimp only at h1
  omega

theorem corner3_not_row (m : ℕ) : ((0 : ℤ), ((m : ℤ) + 2)) ∉ row m := by
  intro h
  have h1 := (mem_row m _ h).2.1
  dsimp only at h1
  omega

theorem cfg_card (m : ℕ) : (cfg m).card = m + 3 := by
  have h3 : ((0 : ℤ), ((m : ℤ) + 2)) ∉ row m := corner3_not_row m
  have h2 : (((m : ℤ) + 2), (0 : ℤ)) ∉ insert ((0 : ℤ), ((m : ℤ) + 2)) (row m) := by
    simp only [Finset.mem_insert, not_or]
    refine ⟨?_, corner2_not_row m⟩
    intro hEq
    have hf := congrArg Prod.fst hEq
    dsimp only at hf
    omega
  have h1 : ((0 : ℤ), (0 : ℤ)) ∉
      insert (((m : ℤ) + 2), (0 : ℤ)) (insert ((0 : ℤ), ((m : ℤ) + 2)) (row m)) := by
    simp only [Finset.mem_insert, not_or]
    refine ⟨?_, ?_, corner1_not_row m⟩
    · intro hEq
      have hf := congrArg Prod.fst hEq
      dsimp only at hf
      omega
    · intro hEq
      have hf := congrArg Prod.snd hEq
      dsimp only at hf
      omega
  rw [cfg]
  first
    | rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, row_card]
    | rw [Finset.card_insert_of_not_mem h1, Finset.card_insert_of_not_mem h2,
        Finset.card_insert_of_not_mem h3, row_card]
  try omega

end O07Refute

/-! ## Part 1 -- the frozen statement, verbatim. -/

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

namespace Erdos1084Upper

/-- The points of `S` on the boundary of its convex hull.
(VERBATIM: `O07_HullSizeLowerBound_SCAFFOLD.lean`) -/
noncomputable def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

end Erdos1084Upper

/-- The frozen O07 statement, verbatim, as a proposition. -/
def O07Statement : Prop :=
  ∀ (k : ℕ) (S : Finset (ℝ^ 2)), Metric.IsSeparated' 1 (S : Set (ℝ^ 2)) →
    S.card = 3 * k ^ 2 + 3 * k + 1 → 6 * k ≤ (Erdos1084Upper.hullPts S).card

/-! ## Part 2 -- plane coordinates. -/

namespace O07Refute

noncomputable def pt2 (x y : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![x, y]

@[simp] theorem pt2_fst (x y : ℝ) : (WithLp.ofLp (pt2 x y)) 0 = x := by simp [pt2]

@[simp] theorem pt2_snd (x y : ℝ) : (WithLp.ofLp (pt2 x y)) 1 = y := by simp [pt2]

theorem ext2 (u v : ℝ^ 2) (h0 : (WithLp.ofLp u) 0 = (WithLp.ofLp v) 0)
    (h1 : (WithLp.ofLp u) 1 = (WithLp.ofLp v) 1) : u = v := by
  ext i
  fin_cases i <;> assumption

theorem coord_add (u v : ℝ^ 2) (i : Fin 2) :
    (WithLp.ofLp (u + v)) i = (WithLp.ofLp u) i + (WithLp.ofLp v) i := by simp

theorem coord_smul (r : ℝ) (u : ℝ^ 2) (i : Fin 2) :
    (WithLp.ofLp (r • u)) i = r * (WithLp.ofLp u) i := by simp

theorem dist_coord (u v : ℝ^ 2) :
    dist u v = Real.sqrt (((WithLp.ofLp u) 0 - (WithLp.ofLp v) 0) ^ 2
      + ((WithLp.ofLp u) 1 - (WithLp.ofLp v) 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- The lattice embedding.  Distinct lattice points are automatically `1`-separated, which
is what makes the witness's separation obligation free of case analysis. -/
noncomputable def emb (p : ℤ × ℤ) : ℝ^ 2 := pt2 (p.1 : ℝ) (p.2 : ℝ)

@[simp] theorem emb_fst (p : ℤ × ℤ) : (WithLp.ofLp (emb p)) 0 = (p.1 : ℝ) := by simp [emb]

@[simp] theorem emb_snd (p : ℤ × ℤ) : (WithLp.ofLp (emb p)) 1 = (p.2 : ℝ) := by simp [emb]

theorem emb_inj : Function.Injective emb := by
  intro p q h
  have h0 : ((p.1 : ℝ)) = ((q.1 : ℝ)) := by
    have hc := congrArg (fun z => (WithLp.ofLp z) 0) h
    simpa using hc
  have h1 : ((p.2 : ℝ)) = ((q.2 : ℝ)) := by
    have hc := congrArg (fun z => (WithLp.ofLp z) 1) h
    simpa using hc
  have e1 : p.1 = q.1 := by exact_mod_cast h0
  have e2 : p.2 = q.2 := by exact_mod_cast h1
  exact Prod.ext e1 e2

theorem int_sq (a b : ℤ) (h : a ≠ b) : (1 : ℝ) ≤ ((a : ℝ) - (b : ℝ)) ^ 2 := by
  have hne : a - b ≠ 0 := sub_ne_zero.mpr h
  have h1 : (1 : ℤ) ≤ (a - b) ^ 2 := by
    rcases lt_or_gt_of_ne hne with hl | hg
    · nlinarith
    · nlinarith
  have h2 := (Int.cast_le (R := ℝ)).mpr h1
  push_cast at h2
  linarith

theorem emb_sep (p q : ℤ × ℤ) (h : p ≠ q) : (1 : ℝ) ≤ dist (emb p) (emb q) := by
  have hkey : (1 : ℝ) ≤ ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 := by
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := by
        intro h2
        exact h (Prod.ext h1 h2)
      have hs := int_sq p.2 q.2 h2
      nlinarith [sq_nonneg ((p.1 : ℝ) - (q.1 : ℝ))]
    · have hs := int_sq p.1 q.1 h1
      nlinarith [sq_nonneg ((p.2 : ℝ) - (q.2 : ℝ))]
  have hnn : (0 : ℝ) ≤ ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 := by
    positivity
  rw [dist_coord]
  simp only [emb_fst, emb_snd]
  exact (Real.le_sqrt (by norm_num) hnn).mpr (by nlinarith)

/-! ## Part 3 -- the triangle, and why its inside is inside. -/

theorem combo3 (K : Set (ℝ^ 2)) (hK : Convex ℝ K) (A B C : ℝ^ 2) (hA : A ∈ K) (hB : B ∈ K)
    (hC : C ∈ K) (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1) :
    a • A + b • B + c • C ∈ K := by
  have key := hK.sum_mem (t := (Finset.univ : Finset (Fin 3))) (w := ![a, b, c])
    (z := ![A, B, C]) (by intro i _; fin_cases i <;> simpa)
    (by simp [Fin.sum_univ_three]; linarith) (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three] using key

/-- The closed triangle `(0,0), (M,0), (0,M)` is inside any convex set holding its corners. -/
theorem tri_mem (M x y : ℝ) (hM : 0 < M) (K : Set (ℝ^ 2)) (hK : Convex ℝ K)
    (hA : pt2 0 0 ∈ K) (hB : pt2 M 0 ∈ K) (hC : pt2 0 M ∈ K) (z : ℝ^ 2)
    (hzx : (WithLp.ofLp z) 0 = x) (hzy : (WithLp.ofLp z) 1 = y)
    (h0 : 0 ≤ x) (h1 : 0 ≤ y) (hs : x + y ≤ M) : z ∈ K := by
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hw0 : 0 ≤ 1 - x / M - y / M := by
    have hd : (x + y) / M ≤ 1 := (div_le_one hM).mpr hs
    have he : x / M + y / M = (x + y) / M := by ring
    linarith
  have hmem := combo3 K hK (pt2 0 0) (pt2 M 0) (pt2 0 M) hA hB hC
    (1 - x / M - y / M) (x / M) (y / M) hw0 (div_nonneg h0 hM.le) (div_nonneg h1 hM.le)
    (by ring)
  have heq : (1 - x / M - y / M) • pt2 0 0 + (x / M) • pt2 M 0 + (y / M) • pt2 0 M = z := by
    refine ext2 _ _ ?_ ?_
    · rw [coord_add, coord_add, coord_smul, coord_smul, coord_smul, pt2_fst, pt2_fst,
        pt2_fst, hzx]
      field_simp
      ring
    · rw [coord_add, coord_add, coord_smul, coord_smul, coord_smul, pt2_snd, pt2_snd,
        pt2_snd, hzy]
      field_simp
      ring
  rwa [heq] at hmem

theorem sq_lt_bound {a b : ℝ} (h : (a - b) ^ 2 < (1 / 2) ^ 2) : b - 1 / 2 < a ∧ a < b + 1 / 2 := by
  have hab : |a - b| < 1 / 2 := by
    nlinarith [sq_abs (a - b), abs_nonneg (a - b)]
  have h1 := abs_lt.mp hab
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

/-- A point at distance `≥ 1/2` from every edge of the triangle is in the hull's INTERIOR. -/
theorem int_mem (M cx cy : ℝ) (hM : 0 < M) (Sset : Finset (ℝ^ 2))
    (hA : pt2 0 0 ∈ (Sset : Set (ℝ^ 2))) (hB : pt2 M 0 ∈ (Sset : Set (ℝ^ 2)))
    (hC : pt2 0 M ∈ (Sset : Set (ℝ^ 2))) (c : ℝ^ 2)
    (hcx : (WithLp.ofLp c) 0 = cx) (hcy : (WithLp.ofLp c) 1 = cy)
    (h0 : 1 / 2 ≤ cx) (h1 : 1 / 2 ≤ cy) (hs : cx + cy ≤ M - 1) :
    c ∈ interior (convexHull ℝ (Sset : Set (ℝ^ 2))) := by
  have hK : Convex ℝ (convexHull ℝ (Sset : Set (ℝ^ 2))) := convex_convexHull ℝ _
  have hsub : (Sset : Set (ℝ^ 2)) ⊆ convexHull ℝ (Sset : Set (ℝ^ 2)) := subset_convexHull ℝ _
  refine mem_interior.mpr ⟨Metric.ball c (1 / 2), ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by norm_num)⟩
  intro z hz
  have hd : dist z c < 1 / 2 := Metric.mem_ball.mp hz
  rw [dist_coord] at hd
  have hnn : (0 : ℝ) ≤ ((WithLp.ofLp z) 0 - (WithLp.ofLp c) 0) ^ 2
      + ((WithLp.ofLp z) 1 - (WithLp.ofLp c) 1) ^ 2 := by positivity
  have hsq : ((WithLp.ofLp z) 0 - (WithLp.ofLp c) 0) ^ 2
      + ((WithLp.ofLp z) 1 - (WithLp.ofLp c) 1) ^ 2 < (1 / 2) ^ 2 := by
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (((WithLp.ofLp z) 0 - (WithLp.ofLp c) 0) ^ 2
      + ((WithLp.ofLp z) 1 - (WithLp.ofLp c) 1) ^ 2)]
  rw [hcx, hcy] at hsq
  obtain ⟨ha1, ha2⟩ := sq_lt_bound (a := (WithLp.ofLp z) 0) (b := cx)
    (by nlinarith [sq_nonneg ((WithLp.ofLp z) 1 - cy)])
  obtain ⟨hb1, hb2⟩ := sq_lt_bound (a := (WithLp.ofLp z) 1) (b := cy)
    (by nlinarith [sq_nonneg ((WithLp.ofLp z) 0 - cx)])
  exact tri_mem M ((WithLp.ofLp z) 0) ((WithLp.ofLp z) 1) hM _ hK (hsub hA) (hsub hB)
    (hsub hC) z rfl rfl (by linarith) (by linarith) (by linarith)

/-! ## Part 4 -- the witness in the plane. -/

noncomputable def SS (m : ℕ) : Finset (ℝ^ 2) := (cfg m).image emb

theorem SS_card (m : ℕ) : (SS m).card = m + 3 := by
  rw [SS, Finset.card_image_of_injective _ emb_inj, cfg_card]

theorem SS_sep (m : ℕ) : Metric.IsSeparated' 1 ((SS m : Finset (ℝ^ 2)) : Set (ℝ^ 2)) := by
  have H : ((SS m : Finset (ℝ^ 2)) : Set (ℝ^ 2)).Pairwise
      (fun a b => (1 : ℝ≥0∞) ≤ edist a b) := by
    intro u hu v hv huv
    simp only [SS, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
    obtain ⟨p, hp, rfl⟩ := hu
    obtain ⟨q, hq, rfl⟩ := hv
    have hpq : p ≠ q := by
      intro hEq
      exact huv (by rw [hEq])
    rw [edist_dist]
    exact ENNReal.one_le_ofReal.mpr (emb_sep p q hpq)
  exact H

theorem emb_corner1 : emb ((0 : ℤ), (0 : ℤ)) = pt2 0 0 := by
  simp [emb]

theorem emb_corner2 (m : ℕ) : emb (((m : ℤ) + 2), (0 : ℤ)) = pt2 ((m : ℝ) + 2) 0 := by
  simp [emb]

theorem emb_corner3 (m : ℕ) : emb ((0 : ℤ), ((m : ℤ) + 2)) = pt2 0 ((m : ℝ) + 2) := by
  simp [emb]

theorem cornerA_mem (m : ℕ) : pt2 0 0 ∈ ((SS m : Finset (ℝ^ 2)) : Set (ℝ^ 2)) := by
  have hc : ((0 : ℤ), (0 : ℤ)) ∈ cfg m := by
    rw [cfg]; exact Finset.mem_insert_self _ _
  have hm : emb ((0 : ℤ), (0 : ℤ)) ∈ SS m := by
    rw [SS]; exact Finset.mem_image_of_mem emb hc
  rw [emb_corner1] at hm
  exact Finset.mem_coe.mpr hm

theorem cornerB_mem (m : ℕ) : pt2 ((m : ℝ) + 2) 0 ∈ ((SS m : Finset (ℝ^ 2)) : Set (ℝ^ 2)) := by
  have hc : (((m : ℤ) + 2), (0 : ℤ)) ∈ cfg m := by
    rw [cfg]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hm : emb (((m : ℤ) + 2), (0 : ℤ)) ∈ SS m := by
    rw [SS]; exact Finset.mem_image_of_mem emb hc
  rw [emb_corner2] at hm
  exact Finset.mem_coe.mpr hm

theorem cornerC_mem (m : ℕ) : pt2 0 ((m : ℝ) + 2) ∈ ((SS m : Finset (ℝ^ 2)) : Set (ℝ^ 2)) := by
  have hc : ((0 : ℤ), ((m : ℤ) + 2)) ∈ cfg m := by
    rw [cfg]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hm : emb ((0 : ℤ), ((m : ℤ) + 2)) ∈ SS m := by
    rw [SS]; exact Finset.mem_image_of_mem emb hc
  rw [emb_corner3] at hm
  exact Finset.mem_coe.mpr hm

/-- Every row point is in the INTERIOR of the hull, so none of them is on the frontier. -/
theorem row_interior (m : ℕ) (p : ℤ × ℤ) (hp : p ∈ row m) :
    emb p ∈ interior (convexHull ℝ ((SS m : Finset (ℝ^ 2)) : Set (ℝ^ 2))) := by
  obtain ⟨hs, hlo, hhi⟩ := mem_row m p hp
  refine int_mem ((m : ℝ) + 2) ((p.1 : ℝ)) ((p.2 : ℝ)) (by positivity) (SS m)
    (cornerA_mem m) (cornerB_mem m) (cornerC_mem m) (emb p) (emb_fst p) (emb_snd p) ?_ ?_ ?_
  · have h1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hlo
    linarith
  · rw [hs]; norm_num
  · have h1 : ((p.1 : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hhi
    rw [hs]
    push_cast
    linarith

/-- ONLY the three corners can be hull points. -/
theorem hull_sub (m : ℕ) : Erdos1084Upper.hullPts (SS m)
    ⊆ ({pt2 0 0, pt2 ((m : ℝ) + 2) 0, pt2 0 ((m : ℝ) + 2)} : Finset (ℝ^ 2)) := by
  intro v hv
  have hvS : v ∈ SS m := (Finset.mem_filter.mp hv).1
  have hvf : v ∈ frontier (convexHull ℝ ((SS m : Finset (ℝ^ 2)) : Set (ℝ^ 2))) :=
    (Finset.mem_filter.mp hv).2
  rw [SS, Finset.mem_image] at hvS
  obtain ⟨p, hp, rfl⟩ := hvS
  rw [cfg] at hp
  simp only [Finset.mem_insert] at hp
  rcases hp with rfl | rfl | rfl | hrow
  · rw [emb_corner1]
    exact Finset.mem_insert_self _ _
  · rw [emb_corner2]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · rw [emb_corner3]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · exact absurd (row_interior m p hrow) hvf.2

theorem hullPts_card_le (m : ℕ) : (Erdos1084Upper.hullPts (SS m)).card ≤ 3 := by
  have h := Finset.card_le_card (hull_sub m)
  have c1 : ({pt2 0 ((m : ℝ) + 2)} : Finset (ℝ^ 2)).card = 1 := Finset.card_singleton _
  have c2 := Finset.card_insert_le (pt2 ((m : ℝ) + 2) 0) ({pt2 0 ((m : ℝ) + 2)} : Finset (ℝ^ 2))
  have c3 := Finset.card_insert_le (pt2 0 0)
    ({pt2 ((m : ℝ) + 2) 0, pt2 0 ((m : ℝ) + 2)} : Finset (ℝ^ 2))
  omega

end O07Refute

/-! ## Part 5 -- the refutation. -/

/-- For EVERY `k ≥ 1` the frozen O07 bound fails, and fails by an unbounded margin: the
witness has `3k²+3k+1` points, is 1-separated, and carries at most THREE hull points
against the demanded `6k`. -/
theorem o07_fails_for_every_k (k : ℕ) (hk : 1 ≤ k) :
    ∃ S : Finset (ℝ^ 2), Metric.IsSeparated' 1 (S : Set (ℝ^ 2)) ∧
      S.card = 3 * k ^ 2 + 3 * k + 1 ∧ (Erdos1084Upper.hullPts S).card ≤ 3 := by
  refine ⟨O07Refute.SS (3 * k ^ 2 + 3 * k - 2), O07Refute.SS_sep _, ?_,
    O07Refute.hullPts_card_le _⟩
  rw [O07Refute.SS_card]
  have h2 : 2 ≤ 3 * k ^ 2 + 3 * k := by nlinarith
  generalize 3 * k ^ 2 + 3 * k = N at h2 ⊢
  omega

/-- THE FROZEN O07 STATEMENT IS FALSE. -/
theorem o07_statement_false : ¬ O07Statement := by
  intro H
  obtain ⟨S, hsep, hcard, hle⟩ := o07_fails_for_every_k 1 le_rfl
  have key := H 1 S hsep hcard
  omega

/-- THE SHARP FORM OF THE DEFECT: it is not that the constant `6k` is too big.  The number of
points of a 1-separated set on the frontier of its convex hull admits **NO lower bound
whatsoever** as a function of the number of points — it stays at `3` while `#S → ∞`.  So no
`hullPts`-based rung of ANY shape can feed O10, and O07 cannot be repaired by weakening its
conclusion. -/
theorem hull_count_has_no_lower_bound (N : ℕ) :
    ∃ S : Finset (ℝ^ 2), Metric.IsSeparated' 1 (S : Set (ℝ^ 2)) ∧ N ≤ S.card ∧
      (Erdos1084Upper.hullPts S).card ≤ 3 := by
  refine ⟨O07Refute.SS N, O07Refute.SS_sep N, ?_, O07Refute.hullPts_card_le N⟩
  rw [O07Refute.SS_card]
  omega

#print axioms o07_fails_for_every_k
#print axioms o07_statement_false
#print axioms hull_count_has_no_lower_bound
