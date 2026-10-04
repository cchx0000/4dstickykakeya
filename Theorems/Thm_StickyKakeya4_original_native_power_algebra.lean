import Theorems.Thm_StickyKakeya4_original_native_projection_failure_comparison
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section

namespace OriginalNativePowerAlgebra
open OriginalNativeProjectionBSGCore OriginalTwoProjectionCartesian
open OriginalWeakAlphabetSelection OriginalKaufmanSharedHost
open OriginalNativeProjectionFailureComparison OriginalNativeStructuredPowerBounds

/-- The native BSG density is computed from the actual source cardinality;
the source mass cancels against the chosen square-root cover scale. -/
theorem native_density_identity {t h N M : ℝ} (ht : 0<t) (hh : 0<h)
    (hN : 0<N) (hM : M^2=N/t^2) :
    originalDensity (t^3/16) N h M=t^5/(16*fiberBound h) := by
  have hJ : 0<fiberBound h := by unfold fiberBound; positivity
  unfold originalDensity
  rw [hM]
  field_simp

/-- Original source density and retained mass have fixed power lower bounds,
with no inverse cardinality or number-of-pieces loss. -/
theorem native_density_retention_lower {t h N M : ℝ} (ht : 0<t)
    (hh : 0<h) (hh1 : h≤1) (hN : 0<N) (hM : M^2=N/t^2) :
    t^5*h^2/(2:ℝ)^10≤originalDensity (t^3/16) N h M ∧
    t^20*h^8/(2:ℝ)^52≤originalRetention (t^3/16) N h M := by
  have hJ : 0<fiberBound h := by unfold fiberBound; positivity
  have hJupper := (original_geometric_cover_power_bounds hh hh1
    (show |(0:ℝ)|≤4/h^2 by simp; positivity)).1
  have hlam : t^5*h^2/(2:ℝ)^10≤originalDensity (t^3/16) N h M := by
    rw [native_density_identity ht hh hN hM]
    apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<16) hJ)).mpr
    have hj := (le_div_iff₀ (sq_pos_of_pos hh)).mp hJupper
    have hm := mul_le_mul_of_nonneg_left hj (show 0≤t^5 by positivity)
    nlinarith only [hm]
  refine ⟨hlam,?_⟩
  have hp := pow_le_pow_left₀ (show 0≤t^5*h^2/(2:ℝ)^10 by positivity) hlam 4
  have hd := div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ)≤4096)
  have hid : (t^5*h^2/(2:ℝ)^10)^4/4096=t^20*h^8/(2:ℝ)^52 := by ring
  rw [hid] at hd
  exact hd

theorem native_balance_upper {t h N M : ℝ} (ht : 0<t) (hh : 0<h)
    (hh1 : h≤1) (hN : 0<N) (hM : M^2=N/t^2) :
    balanceLoss (t^3/8) N M (fiberBound h)≤32768/(t^8*h^2) := by
  have hJupper := (original_geometric_cover_power_bounds hh hh1
    (show |(0:ℝ)|≤4/h^2 by simp; positivity)).1
  have hid : balanceLoss (t^3/8) N M (fiberBound h)=512*fiberBound h/t^8 := by
    unfold balanceLoss
    rw [hM]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ 512*(64/h^2)/t^8 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJupper (by norm_num)) (by positivity)
    _ = _ := by ring

theorem native_strip_upper (n : ℕ) {t : ℝ} (ht : 0<t) (ht1 : t≤1)
    (hlog : ((n:ℝ)+3)^2≤1/t) :
    stripConstant n (1/t) ((1/t)/t) (t^4/32)≤3145728/t^16 := by
  have ht4 : t^4≤1 := by simpa using pow_le_pow_left₀ ht.le ht1 4
  have heps : t^4/32≤1/2 := by linarith only [ht4]
  have hden : 0<1-t^4/32 := by linarith only [heps]
  have hhalf : (1/2:ℝ)≤1-t^4/32 := by linarith only [heps]
  unfold stripConstant
  calc
    _ ≤ (48*(1/t)*((1/t)/t)*(1/t))/((t^4/32)^3*(1-t^4/32)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
    _ ≤ (48*(1/t)*((1/t)/t)*(1/t))/((t^4/32)^3*(1/2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hhalf (by positivity))
    _ = _ := by field_simp; ring

end OriginalNativePowerAlgebra
