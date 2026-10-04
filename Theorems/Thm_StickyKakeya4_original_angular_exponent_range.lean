import Theorems.Thm_StickyKakeya4_original_angular_alphabet_translation
import Theorems.Thm_StickyKakeya4_original_separated_height_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalAngularExponentRange
open Classical FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open OriginalAngularAlphabetTranslation OriginalSeparatedHeightCap
/-- Literal one-dimensional packing of the original source Phi. -/
theorem original_angular_card_upper (Phi : Finset ℝ) {mesh : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hsep : Separated Phi mesh)
    (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) : (Phi.card : ℝ) ≤ 4/mesh := by
  have hs : ∀ z ∈ Phi, ∀ w ∈ Phi, z ≠ w → mesh ≤ |z-w| := by
    intro z hz w hw hzw
    simpa only [Real.dist_eq] using hsep z hz w hw hzw
  have hc := separated_interval_cap Phi hm hs (-1) 2 (by norm_num)
  have heq : Phi.filter (fun z => -1 ≤ z ∧ z ≤ -1+2)=Phi := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    have hh := abs_le.mp (hbox z hz)
    exact ⟨hh.1,by linarith [hh.2]⟩
  rw [heq] at hc
  have hinv : 1 ≤ 1/mesh := (le_div_iff₀ hm).mpr (by simpa using hm1)
  calc
    _ ≤ 2/mesh+2 := hc
    _ ≤ 4/mesh := by
      have htwo : 2/mesh=2*(1/mesh) := by ring
      have hfour : 4/mesh=4*(1/mesh) := by ring
      rw [htwo,hfour]
      linarith only [hinv]
/-- A uniform upper exponent range is derived from original packing and AD,
 rather than inferred from the name AD-regular. The explicit K*mesh budget
 is supplied by the actual small-scale parameter choice. -/
theorem original_angular_exponent_lt_two (Phi : Finset ℝ) (hPhi : Phi.Nonempty)
    {mesh K kappa : ℝ} (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hK : 0 < K)
    (hsep : Separated Phi mesh) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1)
    (hAD : ADBounds Phi mesh K kappa) (hsmall : K*mesh ≤ (1/8:ℝ)) : kappa < 2 := by
  have hl := shifted_card_lower Phi hPhi 0 hm1 hAD
  rw [shifted_card] at hl
  have hlow : (1/mesh)^kappa ≤ (Phi.card : ℝ)*K := (div_le_iff₀ hK).mp hl
  have hu := original_angular_card_upper Phi hm hm1 hsep hbox
  by_contra h
  have hk : (2:ℝ) ≤ kappa := le_of_not_gt h
  have hbase : 1 ≤ 1/mesh := (le_div_iff₀ hm).mpr (by simpa using hm1)
  have hp : (1/mesh)^2 ≤ (1/mesh)^kappa := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hbase hk
  have hh := mul_le_mul_of_nonneg_right
    (hp.trans (hlow.trans (mul_le_mul_of_nonneg_right hu hK.le))) (sq_nonneg mesh)
  have hid₁ : (1/mesh)^2*mesh^2=1 := by field_simp
  have hid₂ : ((4/mesh)*K)*mesh^2=4*K*mesh := by field_simp
  rw [hid₁,hid₂] at hh
  nlinarith
/-- Once the original finite packing gives kappa≤2, all common-mesh C costs
 are uniform in the ORIGINAL exponent, while its original mass is retained. -/
theorem uniform_angular_mesh_cost {K ratio kappa : ℝ} (hratio : 1 ≤ ratio) (hk : kappa ≤ 2) :
    (2:ℝ)^kappa*((2:ℝ)^kappa*K^2*ratio^kappa) ≤ 16*K^2*ratio^2 := by
  have htwo : (2:ℝ)^kappa ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hk
    norm_num at hh
    exact hh
  have hratioPow : ratio^kappa ≤ ratio^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hratio hk
  have hsquare := mul_self_le_mul_self (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) kappa) htwo
  calc
    _ = ((2:ℝ)^kappa*(2:ℝ)^kappa*K^2)*ratio^kappa := by ring
    _ ≤ (16*K^2)*ratio^2 := mul_le_mul
      (mul_le_mul_of_nonneg_right (by nlinarith only [hsquare]) (sq_nonneg K)) hratioPow
      (Real.rpow_nonneg (by linarith : 0 ≤ ratio) kappa) (by positivity)
    _ = _ := by ring
end OriginalAngularExponentRange
