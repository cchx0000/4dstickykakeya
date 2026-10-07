import Theorems.Thm_StickyKakeya4_native_conditional_angular_count_transfer
import Theorems.Thm_StickyKakeya4_native_reference_parent_complete_angular_upper
import Theorems.Thm_StickyKakeya4_native_combined_parent_profiles

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000

noncomputable section
namespace NativeConditionalAngularScaleReadback
open NativeConditionalAngularCountTransfer NativeCommonDirectionPhaseMenu
open NativeSquaredGrainQueries NativeCombinedParentProfiles

lemma relative_width_ratio (s t : ℕ) (ht : 6≤ t) (hts : t≤ s) :
    (64:ℝ)/((2^(s-t+6):ℕ):ℝ)=(64/((2^s:ℕ):ℝ))/(64/((2^t:ℕ):ℝ)) := by
  rw [nested_relative_width s t ht hts,dyadic_sigma t ht]
  simp only [div_eq_mul_inv,one_mul,inv_inv]
  ring

lemma inner_query_product (m s t : ℕ) (ht : 6≤ t) (hts : t≤ s) :
    ((2^(m+t-6):ℕ):ℝ)*((2^(s-t+6):ℕ):ℝ)=((2^m:ℕ):ℝ)*((2^s:ℕ):ℝ) := by
  rw [←Nat.cast_mul,←Nat.cast_mul,←pow_add,←pow_add]
  congr 2
  omega

/-- The actual squared stopping-scale geometry pays both admission of
the sigma parent and the fine end of its relative rho/sigma query. The
fine-window ratio is independent of sigma. -/
theorem actual_nested_scale_budgets {delta r a window : ℝ}
    (hd : 0< delta) (hd1 : delta≤ 1) (hr : 0< r) (hrscale : r≤ delta^a)
    (hw : 0≤ window) (hwa : window≤ a)
    (m s t level : ℕ) (ht : 6≤ t) (hts : t≤ s) (hsm : s≤ m)
    (hlevel : m+s-6≤ level)
    (hdelta : 64*delta≤ r^2) (hMiddle : 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2) :
    let b := m+t-6
    let u := s-t+6
    b≤ level ∧ 6≤ u ∧ u≤ level-b+6 ∧
      delta≤ (64/((2^b:ℕ):ℝ))^2 ∧
      ((((2^b:ℕ):ℝ)*delta/64)/(1/((2^u:ℕ):ℝ)))≤ 
        (((2^b:ℕ):ℝ)*delta/64)^window := by
  intro b u
  have hm6 : 6≤ m := by omega
  have hb6 : 6≤ b := by dsimp [b]; omega
  have hbL : b≤ level := by dsimp [b]; omega
  have hu6 : 6≤ u := by dsimp [u]; omega
  have huL : u≤ level-b+6 := by dsimp [u,b]; omega
  let Delta : ℝ := 64/((2^m:ℕ):ℝ)
  have hD : 0< Delta := by dsimp [Delta]; positivity
  have hrD : r≤ Delta^2 := by nlinarith only [hMiddle,hr]
  have hbPhase : b≤ phaseDepth m := by dsimp [b,phaseDepth]; omega
  have hDInner : Delta^2≤ 64/((2^b:ℕ):ℝ) := horizontal_window m b hm6 hbPhase
  have hdR : delta≤ r^2 := by nlinarith only [hdelta,hd]
  have hSquare : delta≤ (64/((2^b:ℕ):ℝ))^2 :=
    hdR.trans ((pow_le_pow_left₀ hr.le hrD 2).trans (pow_le_pow_left₀ (sq_nonneg Delta) hDInner 2))
  have hN : (64:ℝ)≤ ((2^b:ℕ):ℝ) := by
    exact_mod_cast (show (64:ℕ)≤ 2^b by
      simpa only [show (2:ℕ)^6=64 by norm_num] using Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hb6)
  have hDeltaLocal : delta≤ ((2^b:ℕ):ℝ)*delta/64 := by nlinarith only [hN,hd]
  have hSmallPower : delta^a≤ (((2^b:ℕ):ℝ)*delta/64)^window :=
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 hwa).trans (Real.rpow_le_rpow hd.le hDeltaLocal hw)
  have hQuery : ((((2^b:ℕ):ℝ)*delta/64)/(1/((2^u:ℕ):ℝ)))≤ 64*delta/Delta^2 := by
    have hProd := inner_query_product m s t ht hts
    change ((2^b:ℕ):ℝ)*((2^u:ℕ):ℝ)=((2^m:ℕ):ℝ)*((2^s:ℕ):ℝ) at hProd
    have hsmR : ((2^s:ℕ):ℝ)≤ ((2^m:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hsm
    have hid : ((((2^b:ℕ):ℝ)*delta/64)/(1/((2^u:ℕ):ℝ)))=
        (((2^m:ℕ):ℝ)*((2^s:ℕ):ℝ))*delta/64 := by rw [div_div_eq_mul_div,div_one]; rw [←hProd]; ring
    have hid2 : 64*delta/Delta^2=(((2^m:ℕ):ℝ)*((2^m:ℕ):ℝ))*delta/64 := by
      dsimp [Delta]
      field_simp
    rw [hid,hid2]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmR (Nat.cast_nonneg _)) hd.le) (by norm_num)
  have hQueryR : 64*delta/Delta^2≤ r := (div_le_iff₀ (sq_pos_of_pos hD)).mpr
    (hdelta.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hrD hr.le))
  exact ⟨hbL,hu6,huL,hSquare,hQuery.trans (hQueryR.trans (hrscale.trans hSmallPower))⟩

end NativeConditionalAngularScaleReadback
