import Theorems.Thm_StickyKakeya4_original_planar_tube_parameters
import Theorems.Thm_StickyKakeya4_original_three_dimensional_planar_box_projection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalPlanarTubeProjection
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectionCells OriginalPlanarTubeParameters

abbrev chartProject (b : Frame3) (swap : Bool) (x : Point3) := chart swap (project b x)

def projectedPair (b : Frame3) (swap : Bool) (p q : Point3) : Pair2 :=
  (chartProject b swap p,chartProject b swap q)

lemma chart_distance2 (swap : Bool) (x y : Point2) :
    distance2 (chart swap x) (chart swap y)=distance2 x y := by
  cases swap with
  | false => rfl
  | true =>
    change distance2 x.swap y.swap=distance2 x y
    have h1 := distance2_squared x.swap y.swap
    have h2 := distance2_squared x y
    have h0 : 0 ≤ distance2 x.swap y.swap := dist_nonneg
    have h0' : 0 ≤ distance2 x y := dist_nonneg
    dsimp at h1
    nlinarith only [h1,h2,h0,h0']

lemma chart_linePoint (swap : Bool) (z : Pair2) (t : ℝ) :
    chart swap (OriginalPairStripGeometry.linePoint z t)=
      OriginalPairStripGeometry.linePoint (chart swap z.1,chart swap z.2) t := by
  cases swap <;> rfl

lemma chart_project_linePoint (b : Frame3) (swap : Bool) (p q : Point3) (t : ℝ) :
    chartProject b swap (linePoint3 p q t)=
      OriginalPairStripGeometry.linePoint (projectedPair b swap p q) t := by
  unfold chartProject
  rw [project_linePoint,chart_linePoint]
  rfl

lemma chart_projected_distance_le (b : Frame3) (swap : Bool) (p q : Point3) :
    distance2 (chartProject b swap p) (chartProject b swap q) ≤ distance3 p q := by
  rw [chart_distance2]
  exact projected_distance_le b p q

lemma chart_projected_coordinate_bounds (b : Frame3) (swap : Bool) (x : Point3)
    (hx : ∀ j,|x j| ≤ 1) : |(chartProject b swap x).1| ≤ 3 ∧ |(chartProject b swap x).2| ≤ 3 := by
  have h := original_projected_coordinate_bounds b x hx
  cases swap
  · exact h
  · exact ⟨h.2,h.1⟩

lemma frameCoordinate_linePoint (b : Frame3) (j : Fin 3) (p q : Point3) (t : ℝ) :
    frameCoordinate b j (linePoint3 p q t)=
      frameCoordinate b j p+t*(frameCoordinate b j q-frameCoordinate b j p) := by
  simp only [frameCoordinate,linePoint3,Fin.sum_univ_three]
  ring

lemma frame_distance_le_tangent_normal (b : Frame3) (x y : Point3) :
    distance3 x y ≤ distance2 (project b x) (project b y)+
      |frameCoordinate b 2 x-frameCoordinate b 2 y| := by
  have h := frame_distance_squared b x y
  have hd : 0 ≤ distance3 x y := Real.sqrt_nonneg _
  have hp : 0 ≤ distance2 (project b x) (project b y) := dist_nonneg
  have hn := abs_nonneg (frameCoordinate b 2 x-frameCoordinate b 2 y)
  have hs := sq_abs (frameCoordinate b 2 x-frameCoordinate b 2 y)
  have hm := mul_nonneg hp hn
  nlinarith only [h,hd,hp,hn,hs,hm]

lemma original_pair_affine_graph (z : Pair2) (t : ℝ) (hne : z.2.1-z.1.1≠0) :
    (OriginalPairStripGeometry.linePoint z t).2=
      pairSlope z*(OriginalPairStripGeometry.linePoint z t).1+pairOffset z := by
  have he := original_pair_graph_endpoints z hne
  dsimp [OriginalPairStripGeometry.linePoint]
  rw [he.1,he.2]
  ring

/-- A genuine original 3D pair tube projects into the actual pair's
scalar graph strip in its selected max-coordinate chart. -/
theorem original_pair_tube_scalar_strip (b : Frame3) (swap : Bool) (p q x : Point3)
    (rho : ℝ)
    (hne : (chartProject b swap q).1-(chartProject b swap p).1≠0)
    (hmax : |(chartProject b swap q).2-(chartProject b swap p).2| ≤
      |(chartProject b swap q).1-(chartProject b swap p).1|)
    (hx : x∈physicalTube3 p q rho) :
    |(chartProject b swap x).2-
      (pairSlope (projectedPair b swap p q)*(chartProject b swap x).1+
        pairOffset (projectedPair b swap p q))| ≤ 2*rho := by
  obtain ⟨t,ht⟩ := hx
  have hd := (chart_projected_distance_le b swap x (linePoint3 p q t)).trans ht
  rw [chart_project_linePoint] at hd
  have hc := abs_coordinate_le_distance2 (chartProject b swap x)
    (OriginalPairStripGeometry.linePoint (projectedPair b swap p q) t)
  have hx' := hc.1.trans hd
  have hy' := hc.2.trans hd
  have hs := original_pair_slope_bound (projectedPair b swap p q) hne hmax
  have he := original_pair_affine_graph (projectedPair b swap p q) t hne
  have hid : (chartProject b swap x).2-
      (pairSlope (projectedPair b swap p q)*(chartProject b swap x).1+
        pairOffset (projectedPair b swap p q))=
      ((chartProject b swap x).2-(OriginalPairStripGeometry.linePoint (projectedPair b swap p q) t).2)-
      pairSlope (projectedPair b swap p q)*
        ((chartProject b swap x).1-(OriginalPairStripGeometry.linePoint (projectedPair b swap p q) t).1) := by
    rw [he]
    ring
  rw [hid]
  have ha := abs_sub ((chartProject b swap x).2-
      (OriginalPairStripGeometry.linePoint (projectedPair b swap p q) t).2)
    (pairSlope (projectedPair b swap p q)*((chartProject b swap x).1-
      (OriginalPairStripGeometry.linePoint (projectedPair b swap p q) t).1))
  rw [abs_mul] at ha
  have hm := mul_le_mul hs hx' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  linarith only [ha,hy',hm]

/-- Literal parameter-cell membership follows from the original tube
witness and the proved rounding error, on actual projected source labels. -/
theorem original_pair_tube_cell_projection (b : Frame3) (swap : Bool) (p q x : Point3)
    (rho Delta : ℝ) (hDelta : 0<Delta) (hrho : rho ≤ Delta)
    (hbox : ∀ j,|x j| ≤ 1)
    (hne : (chartProject b swap q).1-(chartProject b swap p).1≠0)
    (hmax : |(chartProject b swap q).2-(chartProject b swap p).2| ≤
      |(chartProject b swap q).1-(chartProject b swap p).1|)
    (hx : x∈physicalTube3 p q rho) :
    OriginalPlanarTubePairCount.InCellTube Delta (pairCell Delta (projectedPair b swap p q))
      (chartProject b swap x) := by
  exact original_pair_strip_in_cell Delta rho (projectedPair b swap p q) (chartProject b swap x)
    hDelta hrho (chart_projected_coordinate_bounds b swap x hbox).1
    (original_pair_tube_scalar_strip b swap p q x rho hne hmax hx)

end OriginalThreeDimensionalPlanarTubeProjection
