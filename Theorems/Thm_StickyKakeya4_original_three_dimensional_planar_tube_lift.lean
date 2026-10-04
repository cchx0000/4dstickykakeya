import Theorems.Thm_StickyKakeya4_original_three_dimensional_planar_tube_projection
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_incidence_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalThreeDimensionalPlanarTubeLift
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectionCells OriginalThreeDimensionalPlanarBoxProjection
open OriginalThreeDimensionalPlanarTubeProjection OriginalPlanarTubeParameters

lemma original_raw_pair_chart_gap (b : Frame3) (swap : Bool) (p q : Point3)
    (c rho Delta r : ℝ) (hrho : 0 ≤ rho) (hr : 0<r) (hDelta1 : Delta ≤ 1)
    (hsmall : 54*rho/r ≤ Delta)
    (hp : |frameCoordinate b 2 p-c| ≤ 3*rho)
    (hq : |frameCoordinate b 2 q-c| ≤ 3*rho) (hsep : r ≤ distance3 p q)
    (hmax : |(chartProject b swap q).2-(chartProject b swap p).2| ≤
      |(chartProject b swap q).1-(chartProject b swap p).1|) :
    r/4 ≤ |(chartProject b swap q).1-(chartProject b swap p).1| := by
  have hm := (div_le_iff₀ hr).mp hsmall
  have hD := mul_le_mul_of_nonneg_right hDelta1 hr.le
  have hscale : 4*(3*rho) ≤ r := by nlinarith only [hm,hD,hrho]
  have hg : r/4 ≤ OriginalPlanarTubePairCount.boxDistance (project b p) (project b q) :=
    original_projected_pair_separation b c (3*rho) r p q hp hq hscale hsep
  rw [← original_chart_distance swap] at hg
  change r/4 ≤ max |(chartProject b swap q).1-(chartProject b swap p).1|
    |(chartProject b swap q).2-(chartProject b swap p).2| at hg
  rwa [max_eq_left hmax] at hg

lemma original_raw_width_le_expanded (p q : Point3) (rho Delta r : ℝ)
    (hr : 0<r) (hDelta : 0 ≤ Delta) (hsmall : 54*rho/r ≤ Delta)
    (hp : ∀ j,|p j| ≤ 1) (hq : ∀ j,|q j| ≤ 1) (hsep : r ≤ distance3 p q) :
    3*rho ≤ Delta := by
  have hm := (div_le_iff₀ hr).mp hsmall
  have hr4 := hsep.trans (OriginalTubeGraphPairGeometry.original_box_distance_le_four p q hp hq)
  have hD := mul_le_mul_of_nonneg_left hr4 hDelta
  nlinarith only [hm,hD,hDelta]

lemma original_graph_horizontal_witness (z : Pair2) (x : Point2)
    (hne : z.2.1-z.1.1≠0) :
    (OriginalPairStripGeometry.linePoint z ((x.1-z.1.1)/(z.2.1-z.1.1))).1=x.1 ∧
    (OriginalPairStripGeometry.linePoint z ((x.1-z.1.1)/(z.2.1-z.1.1))).2=
      pairSlope z*x.1+pairOffset z := by
  have he : (OriginalPairStripGeometry.linePoint z ((x.1-z.1.1)/(z.2.1-z.1.1))).1=x.1 := by
    dsimp [OriginalPairStripGeometry.linePoint]
    field_simp
    ring
  refine ⟨he,?_⟩
  rw [original_pair_affine_graph z _ hne,he]

lemma original_graph_tangent_error (z : Pair2) (x : Point2)
    (hne : z.2.1-z.1.1≠0) :
    distance2 x (OriginalPairStripGeometry.linePoint z ((x.1-z.1.1)/(z.2.1-z.1.1))) ≤
      |x.2-(pairSlope z*x.1+pairOffset z)| := by
  have h := distance2_le_abs_add x
    (OriginalPairStripGeometry.linePoint z ((x.1-z.1.1)/(z.2.1-z.1.1)))
  have he := original_graph_horizontal_witness z x hne
  simpa only [he.1,he.2,sub_self,abs_zero,zero_add] using h

lemma original_graph_parameter_bound (z : Pair2) (x : Point2) (r : ℝ)
    (hr : 0<r) (hgap : r/4 ≤ |z.2.1-z.1.1|)
    (hp : |z.1.1| ≤ 3) (hx : |x.1| ≤ 3) :
    r*|(x.1-z.1.1)/(z.2.1-z.1.1)| ≤ 24 := by
  have hne : z.2.1-z.1.1≠0 := abs_pos.mp ((div_pos hr (by norm_num)).trans_le hgap)
  have he : |(x.1-z.1.1)/(z.2.1-z.1.1)| *|z.2.1-z.1.1|=|x.1-z.1.1| := by
    rw [← abs_mul,div_mul_cancel₀ _ hne]
  have hh := mul_le_mul_of_nonneg_left hgap (abs_nonneg ((x.1-z.1.1)/(z.2.1-z.1.1)))
  rw [he] at hh
  have hnum := abs_sub x.1 z.1.1
  nlinarith only [hh,hnum,hp,hx]

/-- The raw original endpoint slab controls the normal excursion of the
actual affine pair line at the explicit horizontal graph parameter. -/
theorem original_affine_normal_lift_error (b : Frame3) (p q x : Point3)
    (c rho Delta r t : ℝ) (hr : 0<r) (hDelta : 0 ≤ Delta)
    (hsmall : 54*rho/r ≤ Delta) (hwidth : 3*rho ≤ Delta)
    (hp : |frameCoordinate b 2 p-c| ≤ 3*rho)
    (hq : |frameCoordinate b 2 q-c| ≤ 3*rho)
    (hx : |frameCoordinate b 2 x-c| ≤ Delta) (ht : r*|t| ≤ 24) :
    |frameCoordinate b 2 x-frameCoordinate b 2 (linePoint3 p q t)| ≤ 5*Delta := by
  have hm := (div_le_iff₀ hr).mp hsmall
  have hm1 := mul_le_mul_of_nonneg_right hm (abs_nonneg t)
  have hm2 := mul_le_mul_of_nonneg_left ht hDelta
  have htρ : 6*rho*|t| ≤ 3*Delta := by nlinarith only [hm1,hm2,hDelta]
  have hd := slab_normal_difference b c (3*rho) q p hq hp
  have hdt := mul_le_mul_of_nonneg_left hd (abs_nonneg t)
  have ha := abs_sub (frameCoordinate b 2 x-c) (frameCoordinate b 2 p-c)
  have hb := abs_sub ((frameCoordinate b 2 x-c)-(frameCoordinate b 2 p-c))
    (t*(frameCoordinate b 2 q-frameCoordinate b 2 p))
  rw [abs_mul] at hb
  have he : frameCoordinate b 2 x-frameCoordinate b 2 (linePoint3 p q t)=
      ((frameCoordinate b 2 x-c)-(frameCoordinate b 2 p-c))-
        t*(frameCoordinate b 2 q-frameCoordinate b 2 p) := by
    rw [frameCoordinate_linePoint]
    ring
  rw [he]
  nlinarith only [ha,hb,hdt,htρ,hp,hx,hwidth]

/-- A literal slope/intercept cell of the actual projected original pair
lifts to the actual original 3D pair tube. The normal error uses the raw
3rho endpoint slabs; the point itself may occupy the full Delta slab. -/
theorem original_projected_cell_tube_lifts (b : Frame3) (swap : Bool) (p q x : Point3)
    (c rho Delta r : ℝ) (hrho : 0 ≤ rho) (hr : 0<r)
    (hDelta : 0<Delta) (hDelta1 : Delta ≤ 1) (hsmall : 54*rho/r ≤ Delta)
    (hpbox : ∀ j,|p j| ≤ 1) (hqbox : ∀ j,|q j| ≤ 1) (hxbox : ∀ j,|x j| ≤ 1)
    (hp : |frameCoordinate b 2 p-c| ≤ 3*rho)
    (hq : |frameCoordinate b 2 q-c| ≤ 3*rho)
    (hx : |frameCoordinate b 2 x-c| ≤ Delta) (hsep : r ≤ distance3 p q)
    (hmax : |(chartProject b swap q).2-(chartProject b swap p).2| ≤
      |(chartProject b swap q).1-(chartProject b swap p).1|)
    (hcell : OriginalPlanarTubePairCount.InCellTube Delta
      (pairCell Delta (projectedPair b swap p q)) (chartProject b swap x)) :
    x∈physicalTube3 p q (32*Delta) := by
  let z := projectedPair b swap p q
  let y := chartProject b swap x
  let t := (y.1-z.1.1)/(z.2.1-z.1.1)
  have hgap := original_raw_pair_chart_gap b swap p q c rho Delta r hrho hr hDelta1 hsmall hp hq hsep hmax
  have hne : z.2.1-z.1.1≠0 := abs_pos.mp ((div_pos hr (by norm_num)).trans_le hgap)
  have hpcoord := (chart_projected_coordinate_bounds b swap p hpbox).1
  have hxcoord := (chart_projected_coordinate_bounds b swap x hxbox).1
  have ht : r*|t| ≤ 24 := original_graph_parameter_bound z y r hr hgap hpcoord hxcoord
  have hstrip := original_cell_in_pair_strip Delta z y hDelta hxcoord hcell
  have htan : distance2 (project b x) (project b (linePoint3 p q t)) ≤ 20*Delta := by
    have hh := (original_graph_tangent_error z y hne).trans hstrip
    change distance2 (chartProject b swap x) (OriginalPairStripGeometry.linePoint z t) ≤ 20*Delta at hh
    rw [← chart_project_linePoint b swap p q t] at hh
    rwa [chart_distance2] at hh
  have hwidth := original_raw_width_le_expanded p q rho Delta r hr hDelta.le hsmall hpbox hqbox hsep
  have hnorm := original_affine_normal_lift_error b p q x c rho Delta r t hr hDelta.le
    hsmall hwidth hp hq hx ht
  refine ⟨t,?_⟩
  have hd := frame_distance_le_tangent_normal b x (linePoint3 p q t)
  linarith only [hd,htan,hnorm,hDelta]

end OriginalThreeDimensionalPlanarTubeLift
