import Theorems.Thm_StickyKakeya4_native_slice_count_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

noncomputable section
namespace NativeSlicePopulationAlgebra

/-- Explicit numerator, multiplicity and height counts determine a slice
population. The occupied-height normalization is retained in both directions. -/
theorem slice_ratio_bounds {I N Z S H C A B Al Au Zl Zu Ml Mu M : ℝ}
    (hH : 0 < H) (hC : 0 < C) (_hA : 0 < A) (hB : 0 < B)
    (hN : 0 ≤ N) (hS : 0 ≤ S) (hZl : 0 < Zl) (hZu : 0 < Zu)
    (hMl : 0 < Ml) (hMu : 0 < Mu)
    (hread : M*N=I)
    (hSliceUpper : S*Z ≤ C*N) (hSliceLower : N ≤ C*S*Z)
    (hIlower : Al*A ≤ H*I) (hIupper : H*I ≤ Au*A)
    (hZlower : Zl ≤ H*Z) (hZupper : H*Z ≤ Zu)
    (hMlower : Ml*B ≤ M) (hMupper : M ≤ Mu*B) :
    (Al/(C*Zu*Mu))*(A/B) ≤ S ∧ S ≤ ((C*Au)/(Zl*Ml))*(A/B) := by
  have hZ : 0 ≤ Z := by nlinarith only [hZlower,hH,hZl]
  have hlo : Al*A ≤ S*(C*Zu*Mu*B) := by
    calc
      _ ≤ H*I := hIlower
      _ = H*(M*N) := by rw [hread]
      _ ≤ H*((Mu*B)*N) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hMupper hN) hH.le
      _ = (H*(Mu*B))*N := by ring
      _ ≤ (H*(Mu*B))*(C*S*Z) := mul_le_mul_of_nonneg_left hSliceLower (by positivity)
      _ = (C*Mu*B*S)*(H*Z) := by ring
      _ ≤ (C*Mu*B*S)*Zu := mul_le_mul_of_nonneg_left hZupper (by positivity)
      _ = _ := by ring
  have hhi : S*(Zl*Ml*B) ≤ (C*Au)*A := by
    have hsz : S*Zl ≤ C*H*N := by
      calc
        _ ≤ S*(H*Z) := mul_le_mul_of_nonneg_left hZlower hS
        _ = H*(S*Z) := by ring
        _ ≤ H*(C*N) := mul_le_mul_of_nonneg_left hSliceUpper hH.le
        _ = _ := by ring
    calc
      _ = (S*Zl)*(Ml*B) := by ring
      _ ≤ (C*H*N)*(Ml*B) := mul_le_mul_of_nonneg_right hsz (by positivity)
      _ = (C*H)*((Ml*B)*N) := by ring
      _ ≤ (C*H)*(M*N) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hMlower hN) (by positivity)
      _ = C*(H*I) := by rw [hread]; ring
      _ ≤ C*(Au*A) := mul_le_mul_of_nonneg_left hIupper hC.le
      _ = _ := by ring
  constructor
  · rw [div_mul_div_comm]
    exact (div_le_iff₀ (show 0 < C*Zu*Mu*B by positivity)).mpr hlo
  · rw [div_mul_div_comm]
    exact (le_div_iff₀ (show 0 < Zl*Ml*B by positivity)).mpr hhi

/-- The spatial exponent is3-kappa only after the numerator and height
counts have been supplied. It does not follow from multiplicity alone. -/
theorem slice_power_bounds {I N Z S H C r kappa Al Au Zl Zu Ml Mu M : ℝ}
    (hH : 0 < H) (hC : 0 < C) (hr : 0 < r)
    (hN : 0 ≤ N) (hS : 0 ≤ S) (hZl : 0 < Zl) (hZu : 0 < Zu)
    (hMl : 0 < Ml) (hMu : 0 < Mu)
    (hread : M*N=I)
    (hSliceUpper : S*Z ≤ C*N) (hSliceLower : N ≤ C*S*Z)
    (hIlower : Al*r^(-3:ℝ) ≤ H*I) (hIupper : H*I ≤ Au*r^(-3:ℝ))
    (hZlower : Zl ≤ H*Z) (hZupper : H*Z ≤ Zu)
    (hMlower : Ml*r^(-kappa) ≤ M) (hMupper : M ≤ Mu*r^(-kappa)) :
    (Al/(C*Zu*Mu))*r^(kappa-3) ≤ S ∧
      S ≤ ((C*Au)/(Zl*Ml))*r^(kappa-3) := by
  have hh := slice_ratio_bounds hH hC (Real.rpow_pos_of_pos hr (-3)) (Real.rpow_pos_of_pos hr (-kappa))
    hN hS hZl hZu hMl hMu hread hSliceUpper hSliceLower hIlower hIupper hZlower hZupper hMlower hMupper
  have he : r^(-3:ℝ)/r^(-kappa)=r^(kappa-3) := by
    rw [←Real.rpow_sub hr]
    congr 1
    ring
  simpa only [he] using hh

end NativeSlicePopulationAlgebra
