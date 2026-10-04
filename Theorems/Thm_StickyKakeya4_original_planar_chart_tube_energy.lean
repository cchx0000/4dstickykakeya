import Theorems.Thm_StickyKakeya4_original_planar_tube_energy
import Theorems.Thm_StickyKakeya4_original_planar_tube_parameters
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators
namespace OriginalPlanarChartTubeEnergy
open Classical OriginalPlanarTubePairCount OriginalPlanarTubeParameters OriginalPlanarTubeEnergy
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalAveragedSliceEnergy

theorem original_chart_coordinate_bounds (swap : Bool) (x : ℝ × ℝ)
    (hx : |x.1| ≤ 3 ∧ |x.2| ≤ 3) :
    |(chart swap x).1| ≤ 3 ∧ |(chart swap x).2| ≤ 3 := by
  cases swap
  · exact hx
  · exact ⟨hx.2,hx.1⟩

/-- Choosing the actual largest-coordinate chart does not change the
source I1 charge. The original source labels and their masses remain intact. -/
theorem original_chart_slab_tube_square_energy (P : Finset Point3) (T : Finset TubeCell)
    (b : Frame3) (swap : Bool) (c h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hbox : ∀ x∈P,∀ j,|x j| ≤ 1)
    (hslab : ∀ x∈P,|frameCoordinate b 2 x-c| ≤ h)
    (hslope : ∀ z∈T,|h*(z.1:ℝ)| ≤ 2) :
    (∑ z∈T,((tubePoints P (fun x => chart swap (project b x)) h z).card : ℝ)^2) ≤
      120000*sliceEnergy P h := by
  have he := original_planar_tube_square_energy P T (fun x => chart swap (project b x)) h hh hh1
    (fun x hx => original_chart_coordinate_bounds swap _
      (original_projected_coordinate_bounds b x (hbox x hx))) hslope
  simp only [original_chart_distance] at he
  have hsum : (∑ x∈P,∑ y∈P,1/max (boxDistance (project b x) (project b y)) h) ≤
      4*sliceEnergy P h := by
    calc
      _ ≤ ∑ x∈P,∑ y∈P,4/max (distance3 x y) h := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        exact original_projected_inverse_distance b c h x y hh (hslab x hx) (hslab y hy)
      _ = _ := by simp only [sliceEnergy,slicePotential,Finset.mul_sum,mul_one_div]
  nlinarith only [he,hsum]

end OriginalPlanarChartTubeEnergy
