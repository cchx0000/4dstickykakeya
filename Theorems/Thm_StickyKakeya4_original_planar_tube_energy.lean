import Theorems.Thm_StickyKakeya4_original_planar_tube_pair_count
import Theorems.Thm_StickyKakeya4_original_three_dimensional_slab_projection
import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_energy_basic
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open scoped BigOperators
namespace OriginalPlanarTubeEnergy
open Classical OriginalPlanarTubePairCount
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalAveragedSliceEnergy

def tubePoints {α : Type*} (P : Finset α) (f : α → ℝ × ℝ)
    (h : ℝ) (z : TubeCell) : Finset α := P.filter (fun x => InCellTube h z (f x))
def tubesThrough {α : Type*} (T : Finset TubeCell) (f : α → ℝ × ℝ)
    (h : ℝ) (x y : α) : Finset TubeCell :=
  T.filter (fun z => InCellTube h z (f x) ∧ InCellTube h z (f y))

/-- The exact source-label identity retains every original point even when
its projected image coincides with another image. -/
theorem original_planar_square_sum_swap {α : Type*} (P : Finset α)
    (T : Finset TubeCell) (f : α → ℝ × ℝ) (h : ℝ) :
    (∑ z∈T,((tubePoints P f h z).card : ℝ)^2)=
      ∑ x∈P,∑ y∈P,((tubesThrough T f h x y).card : ℝ) := by
  have hcard (z : TubeCell) : ((tubePoints P f h z).card : ℝ)=
      ∑ x∈P,if InCellTube h z (f x) then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [tubePoints]
  have hsquare (z : TubeCell) : ((tubePoints P f h z).card : ℝ)^2=
      ∑ x∈P,∑ y∈P,if InCellTube h z (f x) ∧ InCellTube h z (f y)
        then (1:ℝ) else 0 := by
    rw [hcard,pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    apply Finset.sum_congr rfl
    intro y _hy
    by_cases hx : InCellTube h z (f x) <;> by_cases hy : InCellTube h z (f y) <;> simp [hx,hy]
  calc
    _ = ∑ z∈T,∑ x∈P,∑ y∈P,if InCellTube h z (f x) ∧ InCellTube h z (f y)
          then (1:ℝ) else 0 := Finset.sum_congr rfl (fun z _ => hsquare z)
    _ = ∑ x∈P,∑ y∈P,∑ z∈T,if InCellTube h z (f x) ∧ InCellTube h z (f y)
          then (1:ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← Finset.sum_filter]
      simp [tubesThrough]

/-- A true grid-tube family is paid by the original-label projected I1
energy. Projected source multiplicities are preserved exactly. -/
theorem original_planar_tube_square_energy {α : Type*} (P : Finset α)
    (T : Finset TubeCell) (f : α → ℝ × ℝ) (h : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hbox : ∀ x∈P,|(f x).1| ≤ 3 ∧ |(f x).2| ≤ 3)
    (hslope : ∀ z∈T,|h*(z.1:ℝ)| ≤ 2) :
    (∑ z∈T,((tubePoints P f h z).card : ℝ)^2) ≤
      30000*(∑ x∈P,∑ y∈P,1/max (boxDistance (f x) (f y)) h) := by
  rw [original_planar_square_sum_swap]
  calc
    _ ≤ ∑ x∈P,∑ y∈P,30000/max (boxDistance (f x) (f y)) h := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have hd : boxDistance (f x) (f y) ≤ 6 := by
        apply max_le
        · exact (abs_sub _ _).trans (by linarith only [(hbox x hx).1,(hbox y hy).1])
        · exact (abs_sub _ _).trans (by linarith only [(hbox x hx).2,(hbox y hy).2])
      apply (le_div_iff₀ (lt_max_of_lt_right hh)).mpr
      exact original_planar_two_point_cell_count (tubesThrough T f h x y) h (f x) (f y)
        hh hh1 hd (fun z hz => hslope z (Finset.mem_filter.mp hz).1)
        (fun z hz => (Finset.mem_filter.mp hz).2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2)
    _ = _ := by simp only [Finset.mul_sum,mul_one_div]

/-- The orthogonal projection of an actual slab compares truncated
inverse distances without any injectivity assumption. -/
theorem original_projected_inverse_distance (b : Frame3) (c h : ℝ)
    (x y : Point3) (hh : 0 < h)
    (hx : |frameCoordinate b 2 x-c| ≤ h)
    (hy : |frameCoordinate b 2 y-c| ≤ h) :
    1/max (boxDistance (project b x) (project b y)) h ≤
      4/max (distance3 x y) h := by
  let D := boxDistance (project b x) (project b y)
  have hD : 0 ≤ D := (abs_nonneg _).trans (le_max_left _ _)
  have hxD : |(project b x).1-(project b y).1| ≤ D := by
    simpa only [D,boxDistance,abs_sub_comm] using (le_max_left |(project b y).1-(project b x).1|
      |(project b y).2-(project b x).2|)
  have hyD : |(project b x).2-(project b y).2| ≤ D := by
    simpa only [D,boxDistance,abs_sub_comm] using (le_max_right |(project b y).1-(project b x).1|
      |(project b y).2-(project b x).2|)
  have heuc : distance2 (project b x) (project b y) ≤ 2*D := by
    have hx2 := pow_le_pow_left₀ (abs_nonneg _) hxD 2
    have hy2 := pow_le_pow_left₀ (abs_nonneg _) hyD 2
    rw [sq_abs] at hx2 hy2
    have hs := distance2_squared (project b x) (project b y)
    have hn : 0 ≤ distance2 (project b x) (project b y) := dist_nonneg
    nlinarith only [hx2,hy2,hs,hD,hn,sq_nonneg D]
  have hc := original_slab_distance_comparison b c h x y hx hy
  have hmax : max (distance3 x y) h ≤ 4*max D h := by
    apply max_le
    · linarith only [hc,heuc,le_max_left D h,le_max_right D h]
    · linarith only [le_max_right D h,hh]
  exact (div_le_div_iff₀ (lt_max_of_lt_right hh) (lt_max_of_lt_right hh)).mpr (by
    simpa only [one_mul] using hmax)

/-- Every projected grid tube is charged to the ORIGINAL ambient slice
energy. This is the energy needed to transfer richness to its retained core. -/
theorem original_slab_tube_square_energy (P : Finset Point3) (T : Finset TubeCell)
    (b : Frame3) (c h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hbox : ∀ x∈P,∀ j,|x j| ≤ 1)
    (hslab : ∀ x∈P,|frameCoordinate b 2 x-c| ≤ h)
    (hslope : ∀ z∈T,|h*(z.1:ℝ)| ≤ 2) :
    (∑ z∈T,((tubePoints P (project b) h z).card : ℝ)^2) ≤
      120000*sliceEnergy P h := by
  have he := original_planar_tube_square_energy P T (project b) h hh hh1
    (fun x hx => original_projected_coordinate_bounds b x (hbox x hx)) hslope
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

end OriginalPlanarTubeEnergy
