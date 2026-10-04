import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace OriginalCWScaleCancellation

/-- Exact dimension-four cancellation in the ORIGINAL reference family.
 The three counting inputs are the grid coarsening, point/fine-label ancestor
 map, and disjoint full carrier count. No concentration lower bound is input. -/
theorem original_count_scale_cancellation (a b : ℕ) (hab : a+b=3)
    {Qr N Anc Lrho Lcarrier Cpos Cdir Cvol K CW rho sigma Ntotal : ℝ}
    (hrho : 0 < rho) (hsigma : 0 ≤ sigma) (hLrho : 0 ≤ Lrho)
    (hLcarrier : 0 < Lcarrier) (hCpos : 0 ≤ Cpos) (hCdir : 0 ≤ Cdir)
    (hCvol : 0 ≤ Cvol) (hCW : 0 ≤ CW)
    (hcoarse : Qr*rho^(2*a) ≤ 3^a*sigma^a*N)
    (hpairs : N*Lrho ≤ Anc*(Cpos*Cdir))
    (hcarrier : Anc*Lcarrier ≤ CW*(Cvol*rho^a*sigma^b)*Ntotal)
    (hnormalize : sigma^3*Ntotal ≤ K*Lcarrier) :
    Qr*rho^a*Lrho ≤ 3^a*Cpos*Cdir*Cvol*K*CW := by
  have hc : 0 ≤ (3:ℝ)^a*sigma^a := by positivity
  have hbound :
      (Qr*rho^a*Lrho)*(rho^a*Lcarrier) ≤
        (3^a*Cpos*Cdir*Cvol*K*CW)*(rho^a*Lcarrier) := by
    calc
      _ = (Qr*rho^(2*a))*(Lrho*Lcarrier) := by
        rw [two_mul,pow_add]
        ring
      _ ≤ (3^a*sigma^a*N)*(Lrho*Lcarrier) :=
        mul_le_mul_of_nonneg_right hcoarse (mul_nonneg hLrho hLcarrier.le)
      _ = (3^a*sigma^a)*(N*Lrho)*Lcarrier := by ring
      _ ≤ (3^a*sigma^a)*(Anc*(Cpos*Cdir))*Lcarrier := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpairs hc) hLcarrier.le
      _ = (3^a*sigma^a*(Cpos*Cdir))*(Anc*Lcarrier) := by ring
      _ ≤ (3^a*sigma^a*(Cpos*Cdir))*(CW*(Cvol*rho^a*sigma^b)*Ntotal) :=
        mul_le_mul_of_nonneg_left hcarrier (by positivity)
      _ = (3^a*Cpos*Cdir*Cvol*CW*rho^a)*(sigma^(a+b)*Ntotal) := by
        rw [pow_add]
        ring
      _ = (3^a*Cpos*Cdir*Cvol*CW*rho^a)*(sigma^3*Ntotal) := by rw [hab]
      _ ≤ (3^a*Cpos*Cdir*Cvol*CW*rho^a)*(K*Lcarrier) :=
        mul_le_mul_of_nonneg_left hnormalize (by positivity)
      _ = (3^a*Cpos*Cdir*Cvol*K*CW)*(rho^a*Lcarrier) := by ring
  exact (mul_le_mul_iff_left₀ (mul_pos (pow_pos hrho a) hLcarrier)).mp hbound

/-- The original global tube upper count and each occupied original carrier
 lower count supply the normalization used above, with no thickened-family CW. -/
theorem carrier_global_normalization {sigma delta Ntotal Lcarrier Kcarrier Kglobal : ℝ}
    (hN : 0 ≤ Ntotal) (hK : 0 ≤ Kcarrier) (hL : 0 ≤ Lcarrier)
    (hglobal : Ntotal*delta^3 ≤ Kglobal)
    (hcarrier : sigma^3 ≤ Kcarrier*Lcarrier*delta^3) :
    sigma^3*Ntotal ≤ (Kcarrier*Kglobal)*Lcarrier := by
  calc
    _ ≤ (Kcarrier*Lcarrier*delta^3)*Ntotal := mul_le_mul_of_nonneg_right hcarrier hN
    _ = (Kcarrier*Lcarrier)*(Ntotal*delta^3) := by ring
    _ ≤ (Kcarrier*Lcarrier)*Kglobal := mul_le_mul_of_nonneg_left hglobal (mul_nonneg hK hL)
    _ = (Kcarrier*Kglobal)*Lcarrier := by ring

/-- The original fine-set AD lower and enlarged-ball upper populations give
 the required directional ratio, retaining its radius-enlargement constant. -/
theorem original_fine_AD_ratio {rho sigma delta kappa KPhi C Lrho Cdir : ℝ}
    (hrho : 0 < rho) (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hK : 0 ≤ KPhi) (hC : 0 ≤ C)
    (hlower : (rho/delta)^kappa ≤ KPhi*Lrho)
    (hupper : Cdir ≤ KPhi*C^kappa*(sigma/delta)^kappa) :
    Cdir*(rho/sigma)^kappa ≤ (KPhi^2*C^kappa)*Lrho := by
  have hR : 0 ≤ (rho/sigma)^kappa := Real.rpow_nonneg (by positivity) _
  have hCp : 0 ≤ C^kappa := Real.rpow_nonneg hC _
  have hid : (sigma/delta)^kappa*(rho/sigma)^kappa=(rho/delta)^kappa := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ sigma/delta) (by positivity : 0 ≤ rho/sigma)]
    congr 1
    field_simp
  calc
    _ ≤ (KPhi*C^kappa*(sigma/delta)^kappa)*(rho/sigma)^kappa :=
      mul_le_mul_of_nonneg_right hupper hR
    _ = (KPhi*C^kappa)*(rho/delta)^kappa := by rw [mul_assoc,hid]
    _ ≤ (KPhi*C^kappa)*(KPhi*Lrho) :=
      mul_le_mul_of_nonneg_left hlower (mul_nonneg hK hCp)
    _ = (KPhi^2*C^kappa)*Lrho := by ring

/-- Combine the derived count with the derived original AD ratio. This keeps
 the sole surviving scale ratio explicit, ready for Qr >= Q*rho^(-a). -/
theorem original_CW_ratio_lower (a : ℕ)
    {Qr rho sigma kappa Lrho Cdir Cbase Kad CW : ℝ}
    (hQr : 0 ≤ Qr) (hrho : 0 ≤ rho) (hCdir : 0 < Cdir) (hKad : 0 ≤ Kad)
    (hcount : Qr*rho^a*Lrho ≤ Cbase*Cdir*CW)
    (hratio : Cdir*(rho/sigma)^kappa ≤ Kad*Lrho) :
    Qr*rho^a*(rho/sigma)^kappa ≤ Cbase*Kad*CW := by
  have hbound : (Qr*rho^a*(rho/sigma)^kappa)*Cdir ≤ (Cbase*Kad*CW)*Cdir := by
    calc
      _ = (Qr*rho^a)*(Cdir*(rho/sigma)^kappa) := by ring
      _ ≤ (Qr*rho^a)*(Kad*Lrho) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (Qr*rho^a*Lrho)*Kad := by ring
      _ ≤ (Cbase*Cdir*CW)*Kad := mul_le_mul_of_nonneg_right hcount hKad
      _ = (Cbase*Kad*CW)*Cdir := by ring
  exact (mul_le_mul_iff_left₀ hCdir).mp hbound

end OriginalCWScaleCancellation
