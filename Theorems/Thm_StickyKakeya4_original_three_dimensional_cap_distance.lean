import Theorems.Thm_StickyKakeya4_original_three_dimensional_cap_count
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_slab
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalCapDistance
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalUnitNormals OriginalThreeDimensionalCapCount
open OriginalThreeDimensionalTubeSlab

lemma point_gap_coordinate (p q : Point3) (i : Fin 3) :
    |q i-p i|≤pointGap p q := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma separation_le_twice_gap (p q : Point3) (r : ℝ)
    (hr : 0<r) (hsep : r≤distance3 p q) : r≤2*pointGap p q := by
  obtain ⟨i,_hi,hir⟩ := exists_original_large_coordinate p q r hr hsep
  have hh := mul_le_mul_of_nonneg_left (point_gap_coordinate p q i) (by norm_num : (0:ℝ)≤2)
  exact hir.trans hh

/-- Physical Euclidean endpoint separation turns the exact finite grid cap
count into the transverse one-dimensional estimate used in angular packing. -/
theorem original_separated_cap_count (S : Finset DirectionLabel) (rho w r : ℝ)
    (p q n : Point3) (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hr : 0<r) (hsep : r≤distance3 p q)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hn : ∀ i, |n i|≤1)
    (hS : S⊆normalGrid rho)
    (hband : ∀ d∈S, |value rho d q-value rho d p|≤3*rho)
    (hcap : ∀ d∈S, distance3 (unitNormal rho d) n≤w) :
    (S.card : ℝ)*rho*r≤360000*w := by
  have hc := original_normal_cap_count S rho w p q n hrho hrhow hwsmall hp hq hn hS hband
    (fun d hd i => (original_coordinate_le_distance (unitNormal rho d) n i).trans (hcap d hd))
  have hrg : r≤2*max (pointGap p q) rho :=
    (separation_le_twice_gap p q r hr hsep).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num : (0:ℝ)≤2))
  have hm := mul_le_mul_of_nonneg_left hrg (show (0:ℝ)≤S.card*rho by positivity)
  nlinarith only [hc,hm]

def euclideanCapBand (rho w : ℝ) (p q n : Point3) : Finset DirectionLabel :=
  (normalGrid rho).filter (fun d => |value rho d q-value rho d p|≤3*rho ∧
    distance3 (unitNormal rho d) n≤w)

/-- Explicit actual-label upper bound in a Euclidean unit-normal cap. -/
theorem original_euclidean_cap_band_card (rho w r : ℝ) (p q n : Point3)
    (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hr : 0<r) (hsep : r≤distance3 p q)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hunit : ∑ i, (n i)^2=1) :
    ((euclideanCapBand rho w p q n).card : ℝ)≤360000*w/(rho*r) := by
  apply (le_div_iff₀ (mul_pos hrho hr)).mpr
  have hh := original_separated_cap_count (euclideanCapBand rho w p q n) rho w r p q n
    hrho hrhow hwsmall hr hsep hp hq (unit_center_components n hunit)
    (Finset.filter_subset _ _) (fun d hd => (Finset.mem_filter.mp hd).2.1)
    (fun d hd => (Finset.mem_filter.mp hd).2.2)
  nlinarith only [hh]

end OriginalThreeDimensionalCapDistance
