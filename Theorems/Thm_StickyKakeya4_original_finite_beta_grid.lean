import Theorems.Thm_StickyKakeya4_native_original_planar_power_slice
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace OriginalFiniteBetaGrid

/-- The finite menu depends only on the original gain parameter. -/
def binLower (zeta : ℝ) (i : ℕ) : ℝ := (zeta/5)*(6/5:ℝ)^i
def binUpper (zeta : ℝ) (i : ℕ) : ℝ := (6/5:ℝ)*binLower zeta i
/-- The denominator nineteen leaves a strict zeta/171 original-exponent margin. -/
def binGain (zeta : ℝ) (i : ℕ) : ℝ := 2*zeta/(19*binUpper zeta i)
def binCapExponent (zeta epsilon : ℝ) (i : ℕ) : ℝ :=
  (21/20:ℝ)*(51/50:ℝ)*epsilon/binLower zeta i

def meshBeta (delta mu : ℝ) : ℝ := Real.log mu/Real.log delta

/-- The actual source-derived mesh interval gives a genuine logarithmic
parameter in a fixed compact interval, with its exact power identity. -/
theorem original_mesh_beta_spec (delta mu zeta : ℝ)
    (hd : 0 < delta) (hd1 : delta < 1) (hzeta : 0 < zeta)
    (hlower : delta ≤ mu) (hupper : mu ≤ delta^(zeta/5)) :
    0 < mu ∧ mu < 1 ∧ zeta/5 ≤ meshBeta delta mu ∧ meshBeta delta mu ≤ 1 ∧
      delta^(meshBeta delta mu)=mu := by
  have hmu : 0 < mu := hd.trans_le hlower
  have hl : Real.log delta < 0 := Real.log_neg hd hd1
  have hlogLower := Real.log_le_log hd hlower
  have hlogUpper := Real.log_le_log hmu hupper
  rw [Real.log_rpow hd] at hlogUpper
  refine ⟨hmu,hupper.trans_lt (Real.rpow_lt_one hd.le hd1 (by positivity)),?_,?_,?_⟩
  · exact (le_div_iff_of_neg hl).mpr hlogUpper
  · apply (div_le_iff_of_neg hl).mpr
    simpa only [one_mul] using hlogLower
  · rw [Real.rpow_def_of_pos hd]
    have he : Real.log delta*meshBeta delta mu=Real.log mu := by
      dsimp [meshBeta]
      field_simp [ne_of_lt hl]
    rw [he,Real.exp_log hmu]

/-- A literal finite geometric menu covers every possible selected beta.
The menu is chosen before the source and does not invoke continuity of
any later theorem's threshold. -/
theorem exists_original_finite_beta_grid (zeta : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta < 1) :
    ∃ N : ℕ,∀ beta : ℝ,zeta/5 ≤ beta → beta ≤ 1 →
      ∃ i : ℕ,i ≤ N ∧ binLower zeta i ≤ beta ∧ beta ≤ binUpper zeta i ∧ binLower zeta i ≤ 1 := by
  have hb : 0 < zeta/5 := by positivity
  have hb1 : zeta/5 ≤ 1 := by linarith only [hzeta1]
  have hx : (1:ℝ) ≤ 1/(zeta/5) := (le_div_iff₀ hb).mpr (by simpa only [one_mul] using hb1)
  obtain ⟨N,_hNlo,hNhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ) < 6/5)
  refine ⟨N,?_⟩
  intro beta hbeta hbeta1
  have hxBeta : (1:ℝ) ≤ beta/(zeta/5) := (le_div_iff₀ hb).mpr (by simpa only [one_mul] using hbeta)
  obtain ⟨i,hlo,hhi⟩ := exists_nat_pow_near hxBeta (by norm_num : (1:ℝ) < 6/5)
  have hpow : (6/5:ℝ)^i < (6/5:ℝ)^(N+1) := hlo.trans_lt
    ((div_le_div_of_nonneg_right hbeta1 hb.le).trans_lt hNhi)
  have hiN : i ≤ N := by
    have hh := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 6/5)).mp hpow
    omega
  have hlo' : binLower zeta i ≤ beta := by
    have hh := (le_div_iff₀ hb).mp hlo
    simpa only [binLower,mul_comm] using hh
  have hhi' : beta ≤ binUpper zeta i := by
    have hh := ((div_lt_iff₀ hb).mp hhi).le
    dsimp [binUpper,binLower]
    rw [pow_succ] at hh
    nlinarith only [hh]
  exact ⟨i,hiN,hlo',hhi',hlo'.trans hbeta1⟩

/-- Every fixed menu entry has legitimate A1 parameters. The strict-gain
slack still leaves the cap/gain ratio below one eighth. -/
theorem original_beta_bin_parameter_bounds (zeta epsilon : ℝ) (i : ℕ)
    (hzeta : 0 < zeta) (hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100) :
    0 < binLower zeta i ∧ zeta/5 ≤ binLower zeta i ∧
      0 < binGain zeta i ∧ binGain zeta i ≤ 10/19 ∧
      0 < binCapExponent zeta epsilon i ∧
      binCapExponent zeta epsilon i ≤ binGain zeta i/8 := by
  have hlo : 0 < binLower zeta i := by dsimp [binLower]; positivity
  have hlower : zeta/5 ≤ binLower zeta i := by
    have hh := mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5) : (1:ℝ) ≤ (6/5:ℝ)^i)
      (show 0 ≤ zeta/5 by positivity)
    simpa only [mul_one,binLower] using hh
  have hupper : 0 < binUpper zeta i := by dsimp [binUpper]; positivity
  have hupperLo : zeta/5 ≤ binUpper zeta i := by dsimp [binUpper]; linarith only [hlower,hlo]
  have hgain : 0 < binGain zeta i := by dsimp [binGain]; positivity
  have hgainHi : binGain zeta i ≤ 10/19 := by
    apply (div_le_iff₀ (show 0 < 19*binUpper zeta i by positivity)).mpr
    nlinarith only [hupperLo]
  have hcap : 0 < binCapExponent zeta epsilon i := by dsimp [binCapExponent]; positivity
  refine ⟨hlo,hlower,hgain,hgainHi,hcap,?_⟩
  unfold binCapExponent binGain
  rw [div_div]
  apply (div_le_div_iff₀ hlo (show 0 < (19*binUpper zeta i)*8 by positivity)).mpr
  have hnumeric : ((21/20:ℝ)*(51/50:ℝ)*epsilon)*(19*(6/5:ℝ)*8) ≤ 2*zeta := by
    linarith only [hepsmall,hzeta]
  have hh := mul_le_mul_of_nonneg_right hnumeric hlo.le
  dsimp [binUpper]
  nlinarith only [hh]

end OriginalFiniteBetaGrid
