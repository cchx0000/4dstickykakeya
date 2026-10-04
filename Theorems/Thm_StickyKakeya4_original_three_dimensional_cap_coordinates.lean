import Theorems.Thm_StickyKakeya4_original_three_dimensional_unit_normals
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
namespace OriginalThreeDimensionalCapCoordinates
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalUnitNormals

lemma actual_grid_coefficients (rho : ℝ) (d : DirectionLabel)
    (hrho : 0<rho) (hrho1 : rho≤1) (hd : d∈normalGrid rho) :
    |rho*(d.2.1:ℝ)|≤4 ∧ |rho*(d.2.2:ℝ)|≤1 := by
  obtain ⟨_he,hpair⟩ := Finset.mem_product.mp hd
  obtain ⟨hk,hl⟩ := Finset.mem_product.mp hpair
  obtain ⟨hklo,hkhi⟩ := Finset.mem_Icc.mp hk
  have hkloR : -(⌈3/rho⌉:ℤ)≤(d.2.1:ℝ) := by exact_mod_cast hklo
  have hkhiR : (d.2.1:ℝ)≤(⌈3/rho⌉:ℤ) := by exact_mod_cast hkhi
  have habs : |(d.2.1:ℝ)|≤(⌈3/rho⌉:ℤ) := abs_le.mpr ⟨hkloR,hkhiR⟩
  have hceil := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (3/rho)) hrho
  have hid : (3/rho+1)*rho=3+rho := by field_simp
  rw [hid] at hceil
  have hmul := mul_le_mul_of_nonneg_left habs hrho.le
  have hv := free_grid_value rho hrho d.2.2 hl
  refine ⟨?_,?_⟩
  · rw [abs_mul,abs_of_pos hrho]
    nlinarith only [hmul,hceil,hrho1]
  · rw [abs_of_nonneg hv.1]
    exact hv.2

lemma actual_normal_length_le_five (rho : ℝ) (d : DirectionLabel)
    (hrho : 0<rho) (hrho1 : rho≤1) (hd : d∈normalGrid rho) :
    normalLength rho d≤5 := by
  have hb := actual_grid_coefficients rho d hrho hrho1 hd
  have hu : (rho*(d.2.1:ℝ))^2≤16 := by nlinarith only [sq_abs (rho*(d.2.1:ℝ)),hb.1,abs_nonneg (rho*(d.2.1:ℝ))]
  have hv : (rho*(d.2.2:ℝ))^2≤1 := by nlinarith only [sq_abs (rho*(d.2.2:ℝ)),hb.2,abs_nonneg (rho*(d.2.2:ℝ))]
  have hs : (normalLength rho d)^2=(rho*d.2.1)^2+(rho*d.2.2)^2+1 := Real.sq_sqrt (by positivity)
  nlinarith only [hs,hu,hv,normal_length_one_le rho d]

/-- A small actual unit-normal cap lies in a controlled rational-parameter
rectangle in each chart. The denominator is bounded from the actual grid,
not imposed as a new chart regularity certificate. -/
theorem original_normal_cap_coordinates (rho w : ℝ) (d : DirectionLabel) (n : Point3)
    (hrho : 0<rho) (hrho1 : rho≤1) (hd : d∈normalGrid rho)
    (hw : 0≤w) (hwsmall : w≤1/10)
    (hn : ∀ i, |n i|≤1)
    (hcap : ∀ i, |unitNormal rho d i-n i|≤w) :
    1/10≤n (d.1 2) ∧
      |rho*(d.2.1:ℝ)-n (d.1 0)/n (d.1 2)|≤100*w ∧
      |rho*(d.2.2:ℝ)-n (d.1 1)/n (d.1 2)|≤100*w := by
  let L := normalLength rho d
  have hL1 : 1≤L := normal_length_one_le rho d
  have hL5 : L≤5 := actual_normal_length_le_five rho d hrho hrho1 hd
  have hLp : 0<L := by linarith only [hL1]
  have hz : |1/L-n (d.1 2)|≤w := by simpa [unitNormal,L] using hcap (d.1 2)
  have hinv : 1/5≤1/L := (le_div_iff₀ hLp).mpr (by linarith only [hL5])
  have hn2 : 1/10≤n (d.1 2) := by
    have hh := (abs_le.mp hz).2
    linarith only [hh,hinv,hwsmall]
  have hnp : 0<n (d.1 2) := by linarith only [hn2]
  have scalar (U N : ℝ) (hN : |N|≤1) (hc : |U/L-N|≤w) :
      |U-N/n (d.1 2)|≤100*w := by
    have ht := abs_add_le ((U/L-N)*n (d.1 2)) (N*(n (d.1 2)-1/L))
    rw [abs_mul,abs_mul] at ht
    have hz' : |n (d.1 2)-1/L|≤w := by simpa only [abs_sub_comm] using hz
    have hm1 := mul_le_mul hc (hn (d.1 2)) (abs_nonneg _) hw
    have hm2 := mul_le_mul hN hz' (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hsum : |(U/L-N)*n (d.1 2)+N*(n (d.1 2)-1/L)|≤2*w := by
      nlinarith only [ht,hm1,hm2]
    have hid : U*n (d.1 2)-N=L*((U/L-N)*n (d.1 2)+N*(n (d.1 2)-1/L)) := by
      field_simp
      ring
    have hnum : |U*n (d.1 2)-N|≤10*w := by
      rw [hid,abs_mul,abs_of_pos hLp]
      have hh := mul_le_mul hL5 hsum (abs_nonneg _) (by norm_num : (0:ℝ)≤5)
      nlinarith only [hh]
    have he : U-N/n (d.1 2)=(U*n (d.1 2)-N)/n (d.1 2) := by field_simp
    rw [he,abs_div,abs_of_pos hnp]
    apply (div_le_iff₀ hnp).mpr
    have hh := mul_le_mul_of_nonneg_left hn2 (show 0≤100*w by positivity)
    nlinarith only [hnum,hh]
  refine ⟨hn2,scalar _ _ (hn _) ?_,scalar _ _ (hn _) ?_⟩
  · simpa [unitNormal,L] using hcap (d.1 0)
  · simpa [unitNormal,L] using hcap (d.1 1)

end OriginalThreeDimensionalCapCoordinates
