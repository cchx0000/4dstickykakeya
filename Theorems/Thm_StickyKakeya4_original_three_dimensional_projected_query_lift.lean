import Theorems.Thm_StickyKakeya4_original_three_dimensional_planar_tube_lift
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalThreeDimensionalProjectedQueryLift
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectionCells OriginalThreeDimensionalPlanarBoxProjection
open OriginalThreeDimensionalPlanarTubeProjection OriginalThreeDimensionalPlanarTubeLift
open OriginalPlanarTubeParameters

def EuclideanPairTube (z : Pair2) (rho : ℝ) (x : Point2) : Prop :=
  ∃ t : ℝ,distance2 x (OriginalPairStripGeometry.linePoint z t) ≤ rho

lemma original_euclidean_pair_strip (z : Pair2) (x : Point2) (rho : ℝ)
    (hne : z.2.1-z.1.1 ≠ 0) (hmax : |z.2.2-z.1.2| ≤ |z.2.1-z.1.1|)
    (hx : EuclideanPairTube z rho x) :
    |x.2-(pairSlope z*x.1+pairOffset z)| ≤ 2*rho := by
  obtain ⟨t,ht⟩ := hx
  have hd := ht
  have hc := abs_coordinate_le_distance2 x
    (OriginalPairStripGeometry.linePoint z t)
  have hx' := hc.1.trans hd
  have hy' := hc.2.trans hd
  have hs := original_pair_slope_bound z hne hmax
  have he := original_pair_affine_graph z t hne
  have hid : x.2-
      (pairSlope z*x.1+
        pairOffset z)=
      (x.2-(OriginalPairStripGeometry.linePoint z t).2)-
      pairSlope z*
        (x.1-(OriginalPairStripGeometry.linePoint z t).1) := by
    rw [he]
    ring
  rw [hid]
  have ha := abs_sub (x.2-
      (OriginalPairStripGeometry.linePoint z t).2)
    (pairSlope z*(x.1-
      (OriginalPairStripGeometry.linePoint z t).1))
  rw [abs_mul] at ha
  have hm := mul_le_mul hs hx' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  linarith only [ha,hy',hm]

/-- An arbitrary actual projected query tube lifts with its explicit raw-slab error.
This allows pairwise cap transport without inventing a global arbitrary-tube cap. -/
theorem original_projected_query_tube_lifts (b : Frame3) (swap : Bool) (p q x : Point3)
    (c rho Delta r R : ℝ) (hrho : 0 ≤ rho) (hr : 0<r)
    (hDelta : 0<Delta) (hDelta1 : Delta ≤ 1) (hsmall : 54*rho/r ≤ Delta)
    (hpbox : ∀ j,|p j| ≤ 1) (hqbox : ∀ j,|q j| ≤ 1) (hxbox : ∀ j,|x j| ≤ 1)
    (hp : |frameCoordinate b 2 p-c| ≤ 3*rho)
    (hq : |frameCoordinate b 2 q-c| ≤ 3*rho)
    (hx : |frameCoordinate b 2 x-c| ≤ Delta) (hsep : r ≤ distance3 p q)
    (hmax : |(chartProject b swap q).2-(chartProject b swap p).2| ≤
      |(chartProject b swap q).1-(chartProject b swap p).1|)
    (hquery : EuclideanPairTube (projectedPair b swap p q) R (chartProject b swap x)) :
    x∈physicalTube3 p q (2*R+5*Delta) := by
  let z := projectedPair b swap p q
  let y := chartProject b swap x
  let t := (y.1-z.1.1)/(z.2.1-z.1.1)
  have hgap := original_raw_pair_chart_gap b swap p q c rho Delta r hrho hr hDelta1 hsmall hp hq hsep hmax
  have hne : z.2.1-z.1.1≠0 := abs_pos.mp ((div_pos hr (by norm_num)).trans_le hgap)
  have hpcoord := (chart_projected_coordinate_bounds b swap p hpbox).1
  have hxcoord := (chart_projected_coordinate_bounds b swap x hxbox).1
  have ht : r*|t| ≤ 24 := original_graph_parameter_bound z y r hr hgap hpcoord hxcoord
  have hstrip := original_euclidean_pair_strip z y R hne hmax hquery
  have htan : distance2 (project b x) (project b (linePoint3 p q t)) ≤ 2*R := by
    have hh := (original_graph_tangent_error z y hne).trans hstrip
    change distance2 (chartProject b swap x) (OriginalPairStripGeometry.linePoint z t) ≤ 2*R at hh
    rw [← chart_project_linePoint b swap p q t] at hh
    rwa [chart_distance2] at hh
  have hwidth := original_raw_width_le_expanded p q rho Delta r hr hDelta.le hsmall hpbox hqbox hsep
  have hnorm := original_affine_normal_lift_error b p q x c rho Delta r t hr hDelta.le
    hsmall hwidth hp hq hx ht
  refine ⟨t,?_⟩
  have hd := frame_distance_le_tangent_normal b x (linePoint3 p q t)
  linarith only [hd,htan,hnorm,hDelta]

end OriginalThreeDimensionalProjectedQueryLift
