/-
H02_FullTurn -- H2, THE FULL TURN ABOUT AN INTERIOR POINT, in POLAR-FAN form.

Discharges rung H2 of `H00_HullAngle_SCAFFOLD.lean`.  The statement of `h2_full_turn` is
BYTE-FROZEN from that scaffold (lines 101-113); the definitions above it are copied verbatim.

WHAT IS BUILT.  Given `v₀` interior to `convexHull ℝ S` and `h = #(hullPts S) ≥ 3`:
  * `θ w := (cvec v₀ w).arg` -- the argument of the complex displacement `w - v₀`,
    valued in `(-π, π]` for free (`Complex.neg_pi_lt_arg` / `Complex.arg_le_pi`);
  * the polar equations are `Complex.cos_arg` / `Complex.sin_arg` -- `‖z‖ cos (arg z) = z.re`;
  * `θ` is INJECTIVE on `hullPts S` (H2b, load-bearing -- PROVED, never assumed);
  * `T := image θ (hullPts S)` has `#T = h` and is enumerated ascending by
    `Finset.orderEmbOfFin`; `p` and `a` extend it `h`-periodically with `a (i+h) = a i + 2π`;
  * every gap is `≤ π` (H2e) and the telescope is `2π` (H2f).

## DEVIATION FROM THE ARCHITECTURE, and why (recorded per instruction)

H2c said to lift `o02_argument_function`'s `Orientation.oangle` construction.  It is REPLACED by
`Complex.arg`.  Reason: the oangle route needs `Module.Oriented` + `Fact (finrank = 2)`
instances AND an oangle-`toReal` ↔ `cos`/`sin` bridge that does not exist by name on this rev;
`Complex.cos_arg` / `Complex.sin_arg` ARE that bridge, already proved, and `Complex.arg` has
exactly the same `(-π, π]` range.  Nothing is lost: `o02_argument_function` is used downstream
only through its range and gap properties, both of which `arg` has.

H2e said to route the half-plane contradiction through `extremePoints ⊆ hullPts` +
`closure_convexHull_extremePoints` (the map's Risk-1).  That route is NOT TAKEN and is not
needed.  `no_open_halfplane` below is cheaper and uses no extreme-point theory at all:
  * a linear functional attains its minimum over `S` at some `u ∈ S` (`Finset.exists_min_image`);
  * `convexHull_min` pushes that minimum over the whole hull, so `⟪n, u⟫ ≤ ⟪n, v₀⟫`;
  * `u` cannot be interior -- stepping from `u` by `-εn/2` inside the hull would beat the
    minimum -- so `u ∈ frontier`, i.e. `u ∈ hullPts S`;
  * but every hull point was assumed to have `⟪n, · - v₀⟫ > 0`.  Contradiction.
`convex_halfspace_ge` does NOT exist on this rev (probe-confirmed), so the half-space's
convexity is proved inline from the definition.

STATUS: see the `#print axioms` block at the bottom -- that, not this comment, is the receipt.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Finset Filter Metric Real
open scoped Finset ENNReal Classical EuclideanGeometry

noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)
end Metric

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Erdos1084Upper

noncomputable def nbrs (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : Finset (ℝ^ 2) :=
  {u ∈ S | dist v u = 1}

noncomputable def udeg (S : Finset (ℝ^ 2)) (v : ℝ^ 2) : ℕ := (nbrs S v).card

noncomputable def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

/-- `v` lies inside the angle at `p (i+1)` in polar form (VERBATIM from
`O06_InteriorPoint_EndToEnd.lean`, Contract C, sealed 2026-09-05). -/
def InsideAngleAt (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (i : ℕ) : Prop :=
  ∃ α β γ r₁ r₂ r₃ : ℝ,
    0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
    (p i).ofLp 0 = (p (i + 1)).ofLp 0 + r₁ * Real.cos α ∧
    (p i).ofLp 1 = (p (i + 1)).ofLp 1 + r₁ * Real.sin α ∧
    v.ofLp 0 = (p (i + 1)).ofLp 0 + r₂ * Real.cos β ∧
    v.ofLp 1 = (p (i + 1)).ofLp 1 + r₂ * Real.sin β ∧
    (p (i + 2)).ofLp 0 = (p (i + 1)).ofLp 0 + r₃ * Real.cos γ ∧
    (p (i + 2)).ofLp 1 = (p (i + 1)).ofLp 1 + r₃ * Real.sin γ ∧
    0 ≤ β - α ∧ β - α ≤ Real.pi ∧ 0 ≤ γ - β ∧ γ - β ≤ Real.pi ∧ γ - α ≤ Real.pi

/-! ## H2a -- coordinates, the complex displacement, and the polar equations -/

/-- Two points of `ℝ^2` with the same two coordinates are equal.  Proved through the norm so
that no `PiLp`/`WithLp` extensionality lemma name is load-bearing. -/
theorem coord_ext (x y : ℝ^ 2) (h0 : x.ofLp 0 = y.ofLp 0) (h1 : x.ofLp 1 = y.ofLp 1) :
    x = y := by
  have hn : ‖x - y‖ = 0 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, h0, h1]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The displacement of `z` from `v`, read as a complex number. -/
noncomputable def cvec (v z : ℝ^ 2) : ℂ := ⟨z.ofLp 0 - v.ofLp 0, z.ofLp 1 - v.ofLp 1⟩

theorem cvec_re (v z : ℝ^ 2) : (cvec v z).re = z.ofLp 0 - v.ofLp 0 := rfl
theorem cvec_im (v z : ℝ^ 2) : (cvec v z).im = z.ofLp 1 - v.ofLp 1 := rfl

theorem cvec_ne_zero (v z : ℝ^ 2) (hz : z ≠ v) : cvec v z ≠ 0 := by
  intro hc
  refine hz (coord_ext z v ?_ ?_)
  · have := congrArg Complex.re hc
    rw [cvec_re] at this
    simp only [Complex.zero_re] at this
    linarith
  · have := congrArg Complex.im hc
    rw [cvec_im] at this
    simp only [Complex.zero_im] at this
    linarith

theorem cvec_norm_pos (v z : ℝ^ 2) (hz : z ≠ v) : 0 < ‖cvec v z‖ :=
  norm_pos_iff.mpr (cvec_ne_zero v z hz)

theorem cvec_polar0 (v z : ℝ^ 2) (hz : z ≠ v) :
    z.ofLp 0 = v.ofLp 0 + ‖cvec v z‖ * Real.cos (cvec v z).arg := by
  have hne := cvec_ne_zero v z hz
  have hn : ‖cvec v z‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  rw [Complex.cos_arg hne, cvec_re]
  field_simp
  ring

theorem cvec_polar1 (v z : ℝ^ 2) (hz : z ≠ v) :
    z.ofLp 1 = v.ofLp 1 + ‖cvec v z‖ * Real.sin (cvec v z).arg := by
  have hne := cvec_ne_zero v z hz
  have hn : ‖cvec v z‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  rw [Complex.sin_arg, cvec_im]
  field_simp
  ring

/-- The unit vector at argument `φ`. -/
noncomputable def dir (φ : ℝ) : ℝ^ 2 := WithLp.toLp 2 ![Real.cos φ, Real.sin φ]

theorem dir_norm (φ : ℝ) : ‖dir φ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, dir]

theorem inner_dir (φ : ℝ) (x : ℝ^ 2) :
    (inner ℝ (dir φ) x : ℝ) = Real.cos φ * x.ofLp 0 + Real.sin φ * x.ofLp 1 := by
  simp [inner, Fin.sum_univ_two, dir]
  all_goals ring

/-! ## H2a -- a hull point is never the interior centre -/

theorem hull_ne_center (S : Finset (ℝ^ 2)) (v₀ w : ℝ^ 2)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))))
    (hw : w ∈ hullPts S) : w ≠ v₀ := by
  intro hEq
  rw [hullPts, Finset.mem_filter] at hw
  exact hw.2.2 (by rw [hEq]; exact hv₀)

/-! ## H2e (the engine) -- no open half-plane through `v₀` contains every hull point -/

/-- If a direction `n = (cos φ, sin φ)` has `⟪n, w - v₀⟫ > 0` for EVERY hull point `w`, then
`v₀` is not interior to the hull.  This is the whole mathematical content of "a central gap
cannot exceed `π`": a gap `> π` produces exactly such a direction. -/
theorem no_open_halfplane (S : Finset (ℝ^ 2)) (v₀ : ℝ^ 2)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2)))) (φ : ℝ)
    (hpos : ∀ w ∈ hullPts S, 0 < (inner ℝ (dir φ) (w - v₀) : ℝ)) : False := by
  classical
  have hnorm : ‖dir φ‖ = 1 := dir_norm φ
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp at hv₀
    · exact hne
  obtain ⟨u, huS, humin⟩ := S.exists_min_image (fun x => (inner ℝ (dir φ) x : ℝ)) hSne
  -- the half-space `{x | ⟪n,u⟫ ≤ ⟪n,x⟫}` is convex (`convex_halfspace_ge` does not exist here)
  have hconv : Convex ℝ {x : ℝ^ 2 | (inner ℝ (dir φ) u : ℝ) ≤ (inner ℝ (dir φ) x : ℝ)} := by
    intro x hx y hy α β hα hβ hαβ
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hlin : (inner ℝ (dir φ) (α • x + β • y) : ℝ)
        = α * (inner ℝ (dir φ) x : ℝ) + β * (inner ℝ (dir φ) y : ℝ) := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [hlin]
    have hsum : α * (inner ℝ (dir φ) u : ℝ) + β * (inner ℝ (dir φ) u : ℝ)
        = (inner ℝ (dir φ) u : ℝ) := by
      rw [← add_mul, hαβ, one_mul]
    linarith [mul_le_mul_of_nonneg_left hx hα, mul_le_mul_of_nonneg_left hy hβ, hsum]
  have hsub : convexHull ℝ (S : Set (ℝ^ 2))
      ⊆ {x : ℝ^ 2 | (inner ℝ (dir φ) u : ℝ) ≤ (inner ℝ (dir φ) x : ℝ)} := by
    refine convexHull_min ?_ hconv
    intro x hx
    exact humin x (by exact_mod_cast hx)
  have hle : (inner ℝ (dir φ) u : ℝ) ≤ (inner ℝ (dir φ) v₀ : ℝ) := hsub (interior_subset hv₀)
  -- the minimiser lies on the frontier
  have hufr : u ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2))) := by
    refine ⟨subset_closure (subset_convexHull ℝ _ (by exact_mod_cast huS)), ?_⟩
    intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior u hint
    have hdist : dist (u - (ε / 2) • dir φ) u = ε / 2 := by
      rw [dist_eq_norm]
      have hcancel : u - (ε / 2) • dir φ - u = -((ε / 2) • dir φ) := by abel
      rw [hcancel, norm_neg, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
          abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    have hmem : u - (ε / 2) • dir φ ∈ convexHull ℝ (S : Set (ℝ^ 2)) := by
      refine interior_subset (hball ?_)
      rw [Metric.mem_ball, hdist]
      linarith
    have hstep := hsub hmem
    simp only [Set.mem_setOf_eq] at hstep
    rw [inner_sub_right, real_inner_smul_right] at hstep
    have hnn : (inner ℝ (dir φ) (dir φ) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hnorm]; norm_num
    rw [hnn] at hstep
    linarith
  have huH : u ∈ hullPts S := by
    rw [hullPts, Finset.mem_filter]
    exact ⟨huS, hufr⟩
  have hp := hpos u huH
  rw [inner_sub_right] at hp
  linarith

/-! ## H2b -- THE θ-INJECTIVITY (load-bearing; proved, never assumed) -/

/-- Two hull points at the same argument about an interior point coincide.  If they did not,
the nearer one would sit strictly inside the segment from the interior point `v₀` to the
farther one, hence in the interior -- contradicting frontier membership. -/
theorem theta_inj (S : Finset (ℝ^ 2)) (v₀ : ℝ^ 2)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2)))) :
    Set.InjOn (fun z => (cvec v₀ z).arg) (hullPts S : Set (ℝ^ 2)) := by
  classical
  -- the one-sided step, applied twice
  have step : ∀ w₁ w₂ : ℝ^ 2, w₁ ∈ hullPts S → w₂ ∈ hullPts S → ∀ t : ℝ, 0 < t → t < 1 →
      (t * (w₁.ofLp 0 - v₀.ofLp 0) = w₂.ofLp 0 - v₀.ofLp 0) →
      (t * (w₁.ofLp 1 - v₀.ofLp 1) = w₂.ofLp 1 - v₀.ofLp 1) → False := by
    intro w₁ w₂ hw₁ hw₂ t ht0 ht1 hre him
    have hw₁S : w₁ ∈ S := (Finset.mem_filter.mp hw₁).1
    have hcl : w₁ ∈ closure (convexHull ℝ (S : Set (ℝ^ 2))) :=
      subset_closure (subset_convexHull ℝ _ (by exact_mod_cast hw₁S))
    have hcomb : w₂ = (1 - t) • v₀ + t • w₁ := by
      refine coord_ext _ _ ?_ ?_
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          Pi.add_apply]
        linarith [hre]
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          Pi.add_apply]
        linarith [him]
    have hint : w₂ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))) := by
      rw [hcomb]
      exact (convex_convexHull ℝ _).combo_interior_closure_mem_interior hv₀ hcl
        (by linarith) (le_of_lt ht0) (by ring)
    exact (Finset.mem_filter.mp hw₂).2.2 hint
  intro w₁ hw₁' w₂ hw₂' harg
  have hw₁ : w₁ ∈ hullPts S := Finset.mem_coe.mp hw₁'
  have hw₂ : w₂ ∈ hullPts S := Finset.mem_coe.mp hw₂'
  simp only at harg
  have hne1 : w₁ ≠ v₀ := hull_ne_center S v₀ w₁ hv₀ hw₁
  have hne2 : w₂ ≠ v₀ := hull_ne_center S v₀ w₂ hv₀ hw₂
  have hz1 : cvec v₀ w₁ ≠ 0 := cvec_ne_zero v₀ w₁ hne1
  have hz2 : cvec v₀ w₂ ≠ 0 := cvec_ne_zero v₀ w₂ hne2
  have hn1 : (0 : ℝ) < ‖cvec v₀ w₁‖ := norm_pos_iff.mpr hz1
  have hn2 : (0 : ℝ) < ‖cvec v₀ w₂‖ := norm_pos_iff.mpr hz2
  have hiff := (Complex.arg_eq_arg_iff hz1 hz2).mp harg
  set t : ℝ := ‖cvec v₀ w₂‖ / ‖cvec v₀ w₁‖ with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have hkey : ((t : ℝ) : ℂ) * cvec v₀ w₁ = cvec v₀ w₂ := by
    rw [htdef]; push_cast; exact hiff
  have hre : t * (w₁.ofLp 0 - v₀.ofLp 0) = w₂.ofLp 0 - v₀.ofLp 0 := by
    have hc := congrArg Complex.re hkey
    rw [cvec_re] at hc
    simpa [Complex.mul_re, cvec_re] using hc
  have him : t * (w₁.ofLp 1 - v₀.ofLp 1) = w₂.ofLp 1 - v₀.ofLp 1 := by
    have hc := congrArg Complex.im hkey
    rw [cvec_im] at hc
    simpa [Complex.mul_im, cvec_im] using hc
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · exact absurd (step w₁ w₂ hw₁ hw₂ t htpos hlt hre him) (by simp)
  · refine coord_ext _ _ ?_ ?_
    · rw [heq] at hre; linarith
    · rw [heq] at him; linarith
  · exfalso
    refine step w₂ w₁ hw₂ hw₁ (1 / t) (by positivity) (by rw [div_lt_one htpos]; linarith) ?_ ?_
    · field_simp
      linarith [hre]
    · field_simp
      linarith [him]

/-! ## H2 -- THE FULL TURN.  STATEMENT BYTE-FROZEN from `H00_HullAngle_SCAFFOLD.lean`. -/

theorem h2_full_turn (S : Finset (ℝ^ 2)) (h : ℕ)
    (hh : h = (hullPts S).card) (h3 : 3 ≤ h) (v₀ : ℝ^ 2)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ),
      (∀ i, p (i + h) = p i) ∧
      (∀ i < h, p i ∈ hullPts S) ∧
      (∀ w ∈ hullPts S, ∃ i < h, p i = w) ∧
      (∀ i, 0 < r i) ∧
      (∀ i, (p i).ofLp 0 = v₀.ofLp 0 + r i * Real.cos (a i)) ∧
      (∀ i, (p i).ofLp 1 = v₀.ofLp 1 + r i * Real.sin (a i)) ∧
      (∀ i < h, 0 ≤ a (i + 1) - a i) ∧
      (∀ i < h, a (i + 1) - a i ≤ Real.pi) ∧
      (∑ i ∈ Finset.range h, (a (i + 1) - a i) = 2 * Real.pi) := by
  classical
  have hh0 : 0 < h := by omega
  have hhm1 : h - 1 < h := by omega
  have hpi : 0 < Real.pi := Real.pi_pos
  -- H2b: the argument is injective on the hull points
  have hinj : Set.InjOn (fun z => (cvec v₀ z).arg) (hullPts S : Set (ℝ^ 2)) :=
    theta_inj S v₀ hv₀
  -- H2d: the sorted value set
  set T : Finset ℝ := (hullPts S).image (fun z => (cvec v₀ z).arg) with hT
  have hTcard : T.card = h := by
    rw [hT, Finset.card_image_of_injOn hinj, ← hh]
  obtain ⟨e, he⟩ : ∃ e : Fin h → ℝ, ∀ j, e j = T.orderEmbOfFin hTcard j := ⟨_, fun _ => rfl⟩
  have hemono : StrictMono e := by
    intro i j hij
    rw [he, he]
    exact (T.orderEmbOfFin hTcard).strictMono hij
  have hemem : ∀ j : Fin h, e j ∈ T := by
    intro j; rw [he]; exact T.orderEmbOfFin_mem hTcard j
  have hsurjE : ∀ t ∈ T, ∃ j : Fin h, e j = t := by
    intro t ht
    have h1 : t ∈ Set.range (T.orderEmbOfFin hTcard) := by
      rw [Finset.range_orderEmbOfFin]; exact_mod_cast ht
    obtain ⟨j, hj⟩ := h1
    exact ⟨j, by rw [he]; exact hj⟩
  have hex : ∀ j : Fin h, ∃ w, w ∈ hullPts S ∧ (cvec v₀ w).arg = e j := by
    intro j
    have hm := hemem j
    rw [hT, Finset.mem_image] at hm
    obtain ⟨w, hw, hwe⟩ := hm
    exact ⟨w, hw, hwe⟩
  choose q hq1 hq2 using hex
  -- the range of the argument
  have hlo : ∀ j : Fin h, -Real.pi < e j := by
    intro j; rw [← hq2 j]; exact Complex.neg_pi_lt_arg _
  have hhi : ∀ j : Fin h, e j ≤ Real.pi := by
    intro j; rw [← hq2 j]; exact Complex.arg_le_pi _
  -- the h-periodic listing and its polar data
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ^ 2, ∀ i, p i = q ⟨i % h, Nat.mod_lt i hh0⟩ := ⟨_, fun _ => rfl⟩
  obtain ⟨a, hae⟩ : ∃ a : ℕ → ℝ, ∀ i,
      a i = e ⟨i % h, Nat.mod_lt i hh0⟩ + ((i / h : ℕ) : ℝ) * (2 * Real.pi) := ⟨_, fun _ => rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r : ℕ → ℝ, ∀ i, r i = ‖cvec v₀ (p i)‖ := ⟨_, fun _ => rfl⟩
  have hpmem : ∀ i : ℕ, p i ∈ hullPts S := by intro i; rw [hp]; exact hq1 _
  have hpne : ∀ i : ℕ, p i ≠ v₀ := fun i => hull_ne_center S v₀ (p i) hv₀ (hpmem i)
  have hcosa : ∀ i : ℕ, Real.cos (a i) = Real.cos (cvec v₀ (p i)).arg := by
    intro i
    rw [hae, Real.cos_add_nat_mul_two_pi, hp, hq2]
  have hsina : ∀ i : ℕ, Real.sin (a i) = Real.sin (cvec v₀ (p i)).arg := by
    intro i
    rw [hae, Real.sin_add_nat_mul_two_pi, hp, hq2]
  -- the values of `a` at the indices that matter
  have ha_lt : ∀ (i : ℕ) (hi : i < h), a i = e ⟨i, hi⟩ := by
    intro i hi
    rw [hae]
    have h1 : (⟨i % h, Nat.mod_lt i hh0⟩ : Fin h) = ⟨i, hi⟩ := by
      simp only [Fin.mk.injEq]; exact Nat.mod_eq_of_lt hi
    rw [h1]
    have h2 : i / h = 0 := Nat.div_eq_of_lt hi
    rw [h2]
    norm_num
  have ha_h : a h = e ⟨0, hh0⟩ + 2 * Real.pi := by
    rw [hae]
    have h1 : (⟨h % h, Nat.mod_lt h hh0⟩ : Fin h) = ⟨0, hh0⟩ := by
      simp only [Fin.mk.injEq]; exact Nat.mod_self h
    rw [h1]
    have h2 : h / h = 1 := Nat.div_self hh0
    rw [h2]
    norm_num
  -- H2e: THE ENGINE.  A direction seeing every hull point strictly is impossible.
  have hkey : ∀ φ : ℝ, (∀ j : Fin h, 0 < Real.cos (e j - φ)) → False := by
    intro φ hc
    refine no_open_halfplane S v₀ hv₀ φ ?_
    intro w hw
    have hwne : w ≠ v₀ := hull_ne_center S v₀ w hv₀ hw
    have hmemT : (cvec v₀ w).arg ∈ T := by
      rw [hT]; exact Finset.mem_image_of_mem _ hw
    obtain ⟨j, hj⟩ := hsurjE _ hmemT
    have hR : 0 < ‖cvec v₀ w‖ := cvec_norm_pos v₀ w hwne
    have h0 := cvec_polar0 v₀ w hwne
    have h1 := cvec_polar1 v₀ w hwne
    have e0 : (w - v₀).ofLp 0 = ‖cvec v₀ w‖ * Real.cos (cvec v₀ w).arg := by
      have hd : (w - v₀).ofLp 0 = w.ofLp 0 - v₀.ofLp 0 := by simp
      rw [hd, h0]; ring
    have e1 : (w - v₀).ofLp 1 = ‖cvec v₀ w‖ * Real.sin (cvec v₀ w).arg := by
      have hd : (w - v₀).ofLp 1 = w.ofLp 1 - v₀.ofLp 1 := by simp
      rw [hd, h1]; ring
    have hinner : (inner ℝ (dir φ) (w - v₀) : ℝ)
        = ‖cvec v₀ w‖ * Real.cos ((cvec v₀ w).arg - φ) := by
      rw [inner_dir, e0, e1, Real.cos_sub]; ring
    rw [hinner, ← hj]
    exact mul_pos hR (hc j)
  -- H2e case A: an interior gap cannot exceed π
  have hcaseA : ∀ (k : ℕ) (hk : k < h) (hk1 : k + 1 < h),
      e ⟨k + 1, hk1⟩ - e ⟨k, hk⟩ ≤ Real.pi := by
    intro k hk hk1
    by_contra hcon
    push_neg at hcon
    refine hkey ((e ⟨k + 1, hk1⟩ + (e ⟨k, hk⟩ + 2 * Real.pi)) / 2) ?_
    intro j
    have hA := hhi ⟨k + 1, hk1⟩
    have hB := hlo ⟨k, hk⟩
    by_cases hjk : (j : ℕ) ≤ k
    · have hmj : e j ≤ e ⟨k, hk⟩ := by
        refine hemono.monotone ?_
        rw [Fin.le_def]
        show (j : ℕ) ≤ k
        exact hjk
      have hlj := hlo j
      have hshift : Real.cos (e j - (e ⟨k + 1, hk1⟩ + (e ⟨k, hk⟩ + 2 * Real.pi)) / 2)
          = Real.cos ((e j + 2 * Real.pi)
              - (e ⟨k + 1, hk1⟩ + (e ⟨k, hk⟩ + 2 * Real.pi)) / 2) := by
        rw [show (e j + 2 * Real.pi) - (e ⟨k + 1, hk1⟩ + (e ⟨k, hk⟩ + 2 * Real.pi)) / 2
            = (e j - (e ⟨k + 1, hk1⟩ + (e ⟨k, hk⟩ + 2 * Real.pi)) / 2) + 2 * Real.pi by ring,
          Real.cos_add_two_pi]
      rw [hshift]
      refine Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    · push_neg at hjk
      have hmj : e ⟨k + 1, hk1⟩ ≤ e j := by
        refine hemono.monotone ?_
        rw [Fin.le_def]
        show k + 1 ≤ (j : ℕ)
        omega
      have hhj := hhi j
      refine Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  -- H2e case B: the WRAP gap cannot exceed π
  have hcaseB : e ⟨0, hh0⟩ + 2 * Real.pi - e ⟨h - 1, hhm1⟩ ≤ Real.pi := by
    by_contra hcon
    push_neg at hcon
    refine hkey ((e ⟨0, hh0⟩ + e ⟨h - 1, hhm1⟩) / 2) ?_
    intro j
    have h1 : e ⟨0, hh0⟩ ≤ e j := by
      refine hemono.monotone ?_
      rw [Fin.le_def]
      show (0 : ℕ) ≤ (j : ℕ)
      exact Nat.zero_le _
    have h2 : e j ≤ e ⟨h - 1, hhm1⟩ := by
      refine hemono.monotone ?_
      rw [Fin.le_def]
      show (j : ℕ) ≤ h - 1
      have := j.isLt
      omega
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  refine ⟨p, a, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- h-periodicity
    intro i
    rw [hp, hp]
    congr 1
    simp only [Fin.mk.injEq]
    exact Nat.add_mod_right i h
  · -- the listing lands in the hull points
    intro i _
    exact hpmem i
  · -- and covers them
    intro w hw
    have hmemT : (cvec v₀ w).arg ∈ T := by
      rw [hT]; exact Finset.mem_image_of_mem _ hw
    obtain ⟨j, hj⟩ := hsurjE _ hmemT
    refine ⟨(j : ℕ), j.isLt, ?_⟩
    rw [hp]
    have hfj : (⟨(j : ℕ) % h, Nat.mod_lt (j : ℕ) hh0⟩ : Fin h) = j := by
      refine Fin.ext ?_
      show (j : ℕ) % h = (j : ℕ)
      exact Nat.mod_eq_of_lt j.isLt
    rw [hfj]
    refine hinj (Finset.mem_coe.mpr (hq1 j)) (Finset.mem_coe.mpr hw) ?_
    simp only
    rw [hq2 j, hj]
  · -- positive radii
    intro i
    rw [hrd]
    exact cvec_norm_pos v₀ (p i) (hpne i)
  · -- polar equation, first coordinate
    intro i
    rw [hrd, hcosa i]
    exact cvec_polar0 v₀ (p i) (hpne i)
  · -- polar equation, second coordinate
    intro i
    rw [hrd, hsina i]
    exact cvec_polar1 v₀ (p i) (hpne i)
  · -- the gaps are nonnegative
    intro i hi
    rcases Nat.lt_or_ge (i + 1) h with hi1 | hi1
    · rw [ha_lt (i + 1) hi1, ha_lt i hi]
      have hstrict : e ⟨i, hi⟩ < e ⟨i + 1, hi1⟩ := by
        refine hemono ?_
        rw [Fin.lt_def]
        show i < i + 1
        omega
      linarith
    · have hih : i + 1 = h := by omega
      have hA : a (i + 1) = e ⟨0, hh0⟩ + 2 * Real.pi := by rw [hih]; exact ha_h
      have hBv : a i = e ⟨h - 1, hhm1⟩ := by
        rw [ha_lt i hi]
        congr 1
        simp only [Fin.mk.injEq]
        omega
      rw [hA, hBv]
      have hx := hlo ⟨0, hh0⟩
      have hy := hhi ⟨h - 1, hhm1⟩
      linarith
  · -- the gaps are at most π
    intro i hi
    rcases Nat.lt_or_ge (i + 1) h with hi1 | hi1
    · rw [ha_lt (i + 1) hi1, ha_lt i hi]
      exact hcaseA i hi hi1
    · have hih : i + 1 = h := by omega
      have hA : a (i + 1) = e ⟨0, hh0⟩ + 2 * Real.pi := by rw [hih]; exact ha_h
      have hBv : a i = e ⟨h - 1, hhm1⟩ := by
        rw [ha_lt i hi]
        congr 1
        simp only [Fin.mk.injEq]
        omega
      rw [hA, hBv]
      exact hcaseB
  · -- H2f: the telescope
    rw [Finset.sum_range_sub a h, ha_h, ha_lt 0 hh0]
    ring

/-! ## JOIN CHECK -- H2's output IS Contract C's input, kernel-checked.

`o06_angle_sum_of_polar_fan` (`O06_PolarFan_Handoff.lean:217-228, 8cee4a8593`) is taken here as
an explicit hypothesis, its signature transcribed verbatim, so that this file stays standalone
and needs no import.  The kernel then checks that the tuple `h2_full_turn` actually produces
feeds it with NOTHING left over but `hinside` -- which is rung H3, Contract C's own.  A shape
mismatch (an `i < h` that should be `∀ i`, a swapped `a`/`r`, a gap stated the other way round)
would fail HERE rather than at assembly time. -/
theorem h2_feeds_contract_c
    (consumer : ∀ (h : ℕ), 3 ≤ h → ∀ (v : ℝ^ 2) (p : ℕ → ℝ^ 2) (a r : ℕ → ℝ),
      (∀ i, p (i + h) = p i) →
      (∀ i, 0 < r i) →
      (∀ i, (p i).ofLp 0 = v.ofLp 0 + r i * Real.cos (a i)) →
      (∀ i, (p i).ofLp 1 = v.ofLp 1 + r i * Real.sin (a i)) →
      (∀ i, i < h → 0 ≤ a (i + 1) - a i) →
      (∀ i, i < h → a (i + 1) - a i ≤ Real.pi) →
      (∑ i ∈ Finset.range h, (a (i + 1) - a i) = 2 * Real.pi) →
      (∀ i, InsideAngleAt v p i) →
      ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
        = ((h : ℝ) - 2) * Real.pi)
    (S : Finset (ℝ^ 2)) (h : ℕ) (hh : h = (hullPts S).card) (h3 : 3 ≤ h) (v₀ : ℝ^ 2)
    (hv₀ : v₀ ∈ interior (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ p : ℕ → ℝ^ 2,
      (∀ i, p (i + h) = p i) ∧
      (∀ i < h, p i ∈ hullPts S) ∧
      (∀ w ∈ hullPts S, ∃ i < h, p i = w) ∧
      ((∀ i, InsideAngleAt v₀ p i) →
        ∑ i ∈ Finset.range h, EuclideanGeometry.angle (p i) (p (i + 1)) (p (i + 2))
          = ((h : ℝ) - 2) * Real.pi) := by
  obtain ⟨p, a, r, hper, hmem, hsurj, hr, hp0, hp1, hnn, hle, hgap⟩ :=
    h2_full_turn S h hh h3 v₀ hv₀
  exact ⟨p, hper, hmem, hsurj,
    fun hinside => consumer h h3 v₀ p a r hper hr hp0 hp1 hnn hle hgap hinside⟩

end Erdos1084Upper

#print axioms Erdos1084Upper.coord_ext
#print axioms Erdos1084Upper.cvec_polar0
#print axioms Erdos1084Upper.cvec_polar1
#print axioms Erdos1084Upper.no_open_halfplane
#print axioms Erdos1084Upper.theta_inj
#print axioms Erdos1084Upper.h2_full_turn
#print axioms Erdos1084Upper.h2_feeds_contract_c
