import Theorems.Thm_StickyKakeya4_original_finite_beta_grid
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace OriginalFiniteBetaPowerTransport
open OriginalFiniteBetaGrid

/-- One fixed planar regularity exponent works for the full actual mesh
interval. Its half exponent leaves a strict graph-density margin. -/
theorem original_beta_regularity_powers (delta mu zeta eta : ℝ)
    (hd : 0 < delta) (hd1 : delta < 1) (hzeta : 0 < zeta) (heta : 0 < eta)
    (hlower : delta ≤ mu) (hupper : mu ≤ delta^(zeta/5)) :
    delta^(-21*eta) ≤ mu^(-(200*eta/zeta)) ∧
      mu^((200*eta/zeta)/2) < delta^(14*eta) := by
  have hmu : 0 < mu := hd.trans_le hlower
  have ha : 0 < 200*eta/zeta := by positivity
  have hneg := Real.rpow_le_rpow_of_nonpos hmu hupper (show -(200*eta/zeta) ≤ 0 by linarith only [ha])
  have heNeg : (delta^(zeta/5))^(-(200*eta/zeta))=delta^(-40*eta) := by
    rw [← Real.rpow_mul hd.le]
    congr 1
    field_simp
    ring
  rw [heNeg] at hneg
  have hpos := Real.rpow_le_rpow hmu.le hupper (show 0 ≤ (200*eta/zeta)/2 by positivity)
  have hePos : (delta^(zeta/5))^((200*eta/zeta)/2)=delta^(20*eta) := by
    rw [← Real.rpow_mul hd.le]
    congr 1
    field_simp
    ring
  rw [hePos] at hpos
  exact ⟨(Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith only [heta])).trans hneg,
    hpos.trans_lt (Real.rpow_lt_rpow_of_exponent_gt hd hd1 (by linarith only [heta]))⟩

/-- The fixed per-bin gain leaves the explicit zeta/171 margin at the
original mesh, including beta equal to a bin endpoint. -/
theorem original_beta_bin_strict_gain (delta mu zeta beta : ℝ) (i : ℕ)
    (hd : 0 < delta) (hd1 : delta < 1) (hzeta : 0 < zeta)
    (hmesh : delta^beta=mu) (hbeta : beta ≤ binUpper zeta i) :
    mu^(-binGain zeta i) ≤ delta^(-zeta/9+zeta/171) ∧
      mu^(-binGain zeta i) < delta^(-zeta/9) := by
  have hlo : 0 < binLower zeta i := by dsimp [binLower]; positivity
  have hhi : 0 < binUpper zeta i := by dsimp [binUpper]; positivity
  have hg : 0 < binGain zeta i := by dsimp [binGain]; positivity
  have hid : binUpper zeta i*binGain zeta i=2*zeta/19 := by
    dsimp [binGain]
    field_simp
  have hbg := mul_le_mul_of_nonneg_right hbeta hg.le
  rw [hid] at hbg
  have hmargin : mu^(-binGain zeta i) ≤ delta^(-zeta/9+zeta/171) := by
    rw [← hmesh,← Real.rpow_mul hd.le]
    apply Real.rpow_le_rpow_of_exponent_ge hd hd1.le
    nlinarith only [hbg]
  exact ⟨hmargin,hmargin.trans_lt (Real.rpow_lt_rpow_of_exponent_gt hd hd1 (by linarith only [hzeta]))⟩

/-- A single source-independent cutoff pays the factor sixteen in the
literal inherited query radius for every bin, using the exact mesh identity. -/
theorem original_beta_bin_cap_radius (delta mu zeta epsilon beta : ℝ) (i : ℕ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hzeta : 0 < zeta) (hepsilon : 0 < epsilon)
    (hmesh : delta^beta=mu) (hbeta : binLower zeta i ≤ beta)
    (hcut : delta^((51/1000:ℝ)*epsilon) ≤ 1/16) :
    mu^(binCapExponent zeta epsilon i) ≤ delta^((51/50:ℝ)*epsilon)/16 := by
  have hlo : 0 < binLower zeta i := by dsimp [binLower]; positivity
  have he : 0 < binCapExponent zeta epsilon i := by dsimp [binCapExponent]; positivity
  have hid : binLower zeta i*binCapExponent zeta epsilon i=(21/20:ℝ)*(51/50:ℝ)*epsilon := by
    dsimp [binCapExponent]
    field_simp
  have hbg := mul_le_mul_of_nonneg_right hbeta he.le
  rw [hid] at hbg
  calc
    _ = delta^(beta*binCapExponent zeta epsilon i) := by rw [← hmesh,← Real.rpow_mul hd.le]
    _ ≤ delta^((21/20:ℝ)*(51/50:ℝ)*epsilon) := Real.rpow_le_rpow_of_exponent_ge hd hd1 hbg
    _ = delta^((51/50:ℝ)*epsilon)*delta^((51/1000:ℝ)*epsilon) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    _ ≤ delta^((51/50:ℝ)*epsilon)*(1/16) := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hd.le _)
    _ = _ := by ring

end OriginalFiniteBetaPowerTransport
