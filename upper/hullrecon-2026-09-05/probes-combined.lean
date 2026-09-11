import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

open EuclideanGeometry Real Finset
open scoped EuclideanGeometry Real Affine

noncomputable section

/-! ## 0. Ambient: the plane, finrank, orientation instances -/
#check @finrank_euclideanSpace_fin
#check @EuclideanSpace.basisFun
#check @Basis.orientation
#check @Module.Oriented
#check @Module.Oriented.positiveOrientation
-- do the two required instances exist GLOBALLY for EuclideanSpace R (Fin 2)?
section
example : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
#synth Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)
#synth Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)
end

/-! ## 1. Triangle angle sum + unoriented angle basics -/
#check @EuclideanGeometry.angle
#check @EuclideanGeometry.angle_add_angle_add_angle_eq_pi
#check @EuclideanGeometry.angle_nonneg
#check @EuclideanGeometry.angle_le_pi
#check @EuclideanGeometry.angle_comm
#check @EuclideanGeometry.law_cos
#check @EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
#check @EuclideanGeometry.angle_eq_pi_iff_sbtw
#check @EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw
#check @EuclideanGeometry.exterior_angle_eq_angle_add_angle

/-! ## 2a. Orientation.oangle (VECTOR level) -/
#check @Orientation.oangle
#check @Orientation.oangle_add
#check @Orientation.oangle_add_swap
#check @Orientation.oangle_sub_left
#check @Orientation.oangle_sub_right
#check @Orientation.oangle_add_cyc3
#check @Orientation.oangle_rev
#check @Orientation.angle_eq_abs_oangle_toReal
#check @Orientation.oangle_eq_angle_or_eq_neg_angle
#check @Orientation.oangle_eq_zero_iff_sameRay
#check @Orientation.oangle_eq_pi_iff_sameRay_neg
#check @Orientation.oangle_ne_zero_and_ne_pi_iff_linearIndependent
#check @Orientation.oangle_smul_left_of_pos
#check @Orientation.rotation
#check @Orientation.oangle_map

/-! ## 2b. EuclideanGeometry.oangle (AFFINE / POINT level) -/
#check @EuclideanGeometry.oangle
#check @EuclideanGeometry.oangle_add
#check @EuclideanGeometry.oangle_add_swap
#check @EuclideanGeometry.oangle_sub_left
#check @EuclideanGeometry.oangle_sub_right
#check @EuclideanGeometry.oangle_add_cyc3
#check @EuclideanGeometry.oangle_rev
#check @EuclideanGeometry.angle_eq_abs_oangle_toReal
#check @EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle
#check @EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear
#check @EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent
#check @EuclideanGeometry.oangle_eq_pi_iff_sbtw
#check @EuclideanGeometry.oangle_eq_zero_iff_wbtw
#check @EuclideanGeometry.oangle_sign_eq_zero_iff_collinear
#check @AffineSubspace.SSameSide.oangle_sign_eq
#check @AffineSubspace.SOppSide.oangle_sign_eq_neg
#check @EuclideanGeometry.angle_eq_angle_div_two_of_oangle_eq_of_sSameSide

/-! ## 2c. Real.Angle -/
#check @Real.Angle.toReal
#check @Real.Angle.neg_pi_lt_toReal
#check @Real.Angle.toReal_le_pi
#check @Real.Angle.abs_toReal_le_pi
#check @Real.Angle.toReal_coe_eq_self_iff
#check @Real.Angle.coe_toReal
#check @Real.Angle.coe_sub
#check @Real.Angle.coe_add
#check @Real.Angle.toReal_injective
#check @Real.Angle.sign
#check @Real.Angle.sign_eq_zero_iff
#check @Real.Angle.toReal_pi
#synth CircularOrder Real.Angle
#synth LinearOrder Real.Angle

/-! ## 3. Convex hull machinery -/
#check @convexHull
#check @Set.Finite.isCompact_convexHull
#check @Set.Finite.isClosed_convexHull
#check @Set.Finite.convexHull_eq
#check @Finset.convexHull_eq
#check @convexHull_eq_union
#check @Set.extremePoints
#check @extremePoints_convexHull_subset
#check @mem_extremePoints
#check @Convex.mem_extremePoints_iff_mem_diff_convexHull_diff
#check @Convex.mem_extremePoints_iff_convex_diff
#check @IsCompact.extremePoints_nonempty
#check @closure_convexHull_extremePoints
#check @IsExposed
#check @Set.exposedPoints
#check @exposedPoints_subset_extremePoints
#check @IsExposed.eq_inter_halfSpace
#check @ConvexIndependent
#check @Convex.convexIndependent_extremePoints
#check @convexIndependent_set_iff_notMem_convexHull_diff
#check @IsVisible
#check @IsClosed.exists_wbtw_isVisible

/-! ## 3b. Separation / supporting hyperplane -/
#check @geometric_hahn_banach_point_closed
#check @geometric_hahn_banach_closed_point
#check @AffineSubspace.SSameSide
#check @AffineSubspace.WSameSide
#check @AffineSubspace.SOppSide

/-! ## 4. Sorting / enumeration -/
#check @Finset.orderIsoOfFin
#check @Finset.orderEmbOfFin
#check @Finset.sort
#check @Finset.sortedLT_sort
#check @Finset.orderEmbOfFin_mem
#check @Finset.range_orderEmbOfFin
#check @Fintype.monoEquivOfFin
#check @Finset.sum_range_sub
#check @finRotate
#check @finRotate_succ_apply

/-! ## 5. Polygon (NEW in this rev) -/
#check @Polygon
#check @Polygon.vertices
#check @Polygon.HasNondegenerateEdges
#check @Polygon.HasNondegenerateVertices
#check @Polygon.edgePath
#check @Polygon.edgeSet
#check @Polygon.boundary
#check @Polygon.toTriangle
#check @Affine.Triangle.toPolygon
#check @Polygon.HasNondegenerateVertices.three_le

/-! ## 6. NAMES EXPECTED TO NOT EXIST -- documenting the gaps -/
#check @EuclideanGeometry.interiorAngle
#check @Polygon.interiorAngle
#check @Polygon.IsConvex
#check @Polygon.angleSum
#check @Polygon.IsSimple
#check @Set.Finite.convexHull
#check @Convex.frontier
#check @convexHull_frontier_eq
#check @Finset.sortCyclic
#check @EuclideanGeometry.angle_sum_polygon
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

open EuclideanGeometry Real Finset
open scoped EuclideanGeometry Real Affine

noncomputable section

notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

/-! ## A. Corrected names from probe 1 -/
#check @Module.Basis.orientation
#check @monoEquivOfFin
#check @finRotate_apply
#check @Convex.interior
#check @Convex.closure
#check @Convex.combo_interior_closure_mem_interior
#check @Real.Angle.instCircularOrder

/-! ## B. THE INSTANCE ROUTE.  Can `∡` (affine oangle) be used on ℝ^2 at all? -/
section InstanceRoute
-- both instances must be supplied by hand; neither is global.
instance factFinrank2 : Fact (Module.finrank ℝ (ℝ^ 2) = 2) := ⟨finrank_euclideanSpace_fin⟩
instance orientedPlane : Module.Oriented ℝ (ℝ^ 2) (Fin 2) :=
  ⟨((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).orientation⟩

-- with those in scope, the POINT-level oriented angle elaborates on ℝ^2:
example (a b c : ℝ^ 2) : Real.Angle := ∡ a b c
example (a b c : ℝ^ 2) : ℝ := (∡ a b c).toReal
example (a b c : ℝ^ 2) (hab : a ≠ b) (hcb : c ≠ b) : ∠ a b c = |(∡ a b c).toReal| :=
  EuclideanGeometry.angle_eq_abs_oangle_toReal hab hcb

-- and a Finset sum of turning angles elaborates:
example (h : ℕ) (p : ℕ → ℝ^ 2) : ℝ :=
  ∑ i ∈ Finset.range h, (∡ (p i) (p (i+1)) (p (i+2))).toReal

/-! ### (a) STATEMENT SHAPE: interior angle at a hull vertex, unoriented -/
def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}

def vertexPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ Set.extremePoints ℝ (convexHull ℝ (S : Set (ℝ^ 2)))}

example (S : Finset (ℝ^ 2)) (p : ℕ → ℝ^ 2) (i : ℕ) : ℝ := ∠ (p i) (p (i+1)) (p (i+2))

/-! ### (b) STATEMENT SHAPE: the angle sum, over a Polygon -/
example (h : ℕ) (poly : Polygon (ℝ^ 2) h) : Prop :=
  ∑ i : Fin h, ∠ (poly (i-1)) (poly i) (poly (i+1)) = ((h : ℝ) - 2) * π

example (h : ℕ) (p : ℕ → ℝ^ 2) : Prop :=
  ∑ i ∈ Finset.range h, ∠ (p i) (p (i+1)) (p (i+2)) = ((h : ℝ) - 2) * π

/-! ### (c) STATEMENT SHAPE: the cone/packing bound -/
example (S : Finset (ℝ^ 2)) (v : ℝ^ 2) (alpha : ℝ) : Prop :=
  (({u ∈ S | dist v u = 1}).card : ℝ) ≤ 1 + 3 * alpha / π

/-! ### Does the ORIENTED turning-angle sum (2π) even state? -/
example (h : ℕ) (p : ℕ → ℝ^ 2) : Prop :=
  ∑ i ∈ Finset.range h, (π - (∠ (p i) (p (i+1)) (p (i+2)))) = 2 * π

end InstanceRoute

/-! ## C. Sorting: what is actually available -/
-- `Finset.sort` needs Antisymm on the relation; a NON-INJECTIVE key breaks it.
#check @Finset.sort
#check @Finset.orderIsoOfFin
-- there is NO LinearOrder on Real.Angle, and no Finset sort by a circular order:
#check @Finset.sortBy
#check @Finset.sortCircular
#check @List.mergeSort
#check @Finset.exists_ne_map_eq_of_card_lt_of_maps_to
#check @Finset.sum_sdiff
#check @Finset.card_sdiff

/-! ## D. Convex-position / hull-vertex bridges that (b) will need -/
#check @Set.Finite.isClosed_convexHull
#check @IsExtreme
#check @Set.extremePoints_subset
#check @inter_extremePoints_subset_extremePoints_of_subset
#check @Convex.convexIndependent_extremePoints
#check @Wbtw
#check @Sbtw
#check @affineSegment
#check @Collinear
#check @AffineSubspace.SSameSide
#check @AffineSubspace.wSameSide_of_left_mem
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

open EuclideanGeometry Real Finset
open scoped EuclideanGeometry Real Affine Classical

noncomputable section
notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

instance factFinrank2 : Fact (Module.finrank ℝ (ℝ^ 2) = 2) := ⟨finrank_euclideanSpace_fin⟩
instance orientedPlane : Module.Oriented ℝ (ℝ^ 2) (Fin 2) :=
  ⟨((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).orientation⟩

/-! ## A. corrected names -/
#check @extremePoints_subset
#check @intrinsicFrontier_subset_frontier
#check @intrinsicClosure_eq_closure
#check @Sbtw.angle_eq_right
#check @Wbtw.angle_eq_left
#check @EuclideanGeometry.angle_self_of_ne
#check @EuclideanGeometry.angle_self
#check @geometric_hahn_banach_open_point
#check @geometric_hahn_banach_point_closed
#check @Convex.interior_nonempty_iff_affineSpan_eq_top
#synth AddCommGroup Real.Angle
#check @Real.Angle.angle_eq_iff_two_pi_dvd_sub
#check @Real.Angle.coe_nsmul
#check @Real.Angle.coe_zsmul

/-! ## B. Classical filter now works -/
def hullPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))}
def vertexPts (S : Finset (ℝ^ 2)) : Finset (ℝ^ 2) :=
  {v ∈ S | v ∈ Set.extremePoints ℝ (convexHull ℝ (S : Set (ℝ^ 2)))}
example (S : Finset (ℝ^ 2)) : vertexPts S ⊆ S := Finset.filter_subset _ _

/-! ## C. THE SUPPORTING-LINE ROUTE for (c) -- does it actually go through? -/
example (S : Finset (ℝ^ 2)) (v : ℝ^ 2)
    (hv : v ∈ frontier (convexHull ℝ (S : Set (ℝ^ 2)))) :
    ∃ f : StrongDual ℝ (ℝ^ 2), ∀ a ∈ interior (convexHull ℝ (S : Set (ℝ^ 2))), f a < f v := by
  have hconv : Convex ℝ (convexHull ℝ (S : Set (ℝ^ 2))) := convex_convexHull ℝ _
  have hnot : v ∉ interior (convexHull ℝ (S : Set (ℝ^ 2))) := by
    have := hv.2
    simpa using this
  exact geometric_hahn_banach_open_point hconv.interior isOpen_interior hnot

/-! ## D. degeneracy of the triangle angle sum -- p3 may equal p1 or p2 -/
example (a b : ℝ^ 2) (h : b ≠ a) : ∠ a b b + ∠ b b a + ∠ b a b = π :=
  EuclideanGeometry.angle_add_angle_add_angle_eq_pi b h
example (a b : ℝ^ 2) (h : b ≠ a) : ∠ a b a + ∠ b a a + ∠ a a b = π :=
  EuclideanGeometry.angle_add_angle_add_angle_eq_pi a h
-- collinear (degenerate) triangles are FINE: no affine-independence hypothesis anywhere

/-! ## E. Polygon on the plane: the NeZero / Fin-arithmetic gotcha -/
section Poly
variable (h : ℕ) [NeZero h]
example (poly : Polygon (ℝ^ 2) h) : Prop := poly.HasNondegenerateVertices ℝ
example (poly : Polygon (ℝ^ 2) h) : Prop :=
  ∑ i : Fin h, ∠ (poly (i - 1)) (poly i) (poly (i + 1)) = ((h : ℝ) - 2) * π
example (poly : Polygon (ℝ^ 2) h) : Set (ℝ^ 2) := poly.boundary ℝ
end Poly

/-! ## F. the ORIENTED route, which is the only additive one -/
example (v a b c : ℝ^ 2) (ha : a ≠ v) (hb : b ≠ v) (hc : c ≠ v) :
    ∡ a v b + ∡ b v c = ∡ a v c := EuclideanGeometry.oangle_add ha hb hc
example (h : ℕ) (p : ℕ → ℝ^ 2) : Real.Angle := ∑ i ∈ Finset.range h, ∡ (p i) (p (i+1)) (p (i+2))
-- telescoping in Real.Angle:
example (m : ℕ) (a : ℕ → Real.Angle) :
    ∑ i ∈ Finset.range m, (a (i + 1) - a i) = a m - a 0 := Finset.sum_range_sub a m

/-! ## G. things that DO NOT exist (second sweep) -/
#check @EuclideanGeometry.angle_add_angle_eq_angle_of_sbtw
#check @EuclideanGeometry.angle_add_angle_of_wSameSide
#check @Polygon.IsConvexPolygon
#check @Polygon.interiorAngle
#check @convexHull_frontier
#check @extremePoints_subset_frontier
#check @Set.extremePoints_convexHull_eq
#check @EuclideanGeometry.oangle_sum_eq_two_pi
