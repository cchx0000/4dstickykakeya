import Theorems.Thm_StickyKakeya4_native_matrix_height_wholepoint
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section

namespace NativeMatrixHeightBudget
open NativeMatrixHeightWholePoint NativeQuarterScaleParameters

/-- The actual weak source Lipschitz constant pays exactly four epsilon
per prepared height scale, with one explicit fixed factor 144 per scale. -/
theorem palette_le_explicit_power (K : ℕ) {r L epsilon : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (heps : 0 ≤ epsilon)
    (hLip : L ≤ 3*r^(-2*epsilon)) :
    (9*(1+L)^2)^K ≤ (144:ℝ)^K*r^(-(4*(K:ℝ)*epsilon)) := by
  have hu : 1 ≤ r^(-2*epsilon) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith only [heps])
  have hv : 1+L ≤ 4*r^(-2*epsilon) := by linarith only [hLip,hu]
  have hsq := pow_le_pow_left₀ (by linarith only [hL] : 0 ≤ 1+L) hv 2
  have hbase : 9*(1+L)^2 ≤ 144*r^(-4*epsilon) := by
    have hp : (r^(-2*epsilon))^2=r^(-4*epsilon) := by
      rw [←Real.rpow_mul_natCast hr.le]
      congr 1
      ring
    nlinarith only [hsq,hp]
  have hpower : (r^(-4*epsilon))^K=r^(-(4*(K:ℝ)*epsilon)) := by
    rw [←Real.rpow_mul_natCast hr.le]
    congr 1
    ring
  calc
    (9*(1+L)^2)^K ≤ (144*r^(-4*epsilon))^K :=
      pow_le_pow_left₀ (by positivity) hbase K
    _ = (144:ℝ)^K*r^(-(4*(K:ℝ)*epsilon)) := by rw [mul_pow,hpower]

/-- The literal NATURAL palette charge used by the original-point selector
inherits the same estimate. No replacement or additional selection occurs. -/
theorem natural_palette_le_explicit_power (K : ℕ) {r L epsilon : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (heps : 0 ≤ epsilon)
    (hLip : L ≤ 3*r^(-2*epsilon)) :
    ((modulus L)^(2*K):ℝ) ≤ (144:ℝ)^K*r^(-(4*(K:ℝ)*epsilon)) :=
  (modulus_cost L hL K).trans (palette_le_explicit_power K hr hr1 hL heps hLip)

/-- Fix K and the requested charge e first. A positive epsilon cap and
radius cutoff are then chosen before ANY source radius or Lipschitz bound.
The same choices work for every smaller nonnegative actual epsilon. -/
theorem exists_uniform_palette_cutoff (K : ℕ) (e : ℝ) (he : 0 < e) :
    ∃epsilon0 r0 : ℝ,0 < epsilon0 ∧ epsilon0 ≤ e/(16*((K:ℝ)+1)) ∧
      0 < r0 ∧ r0 ≤ 1 ∧
      ∀r L epsilon : ℝ,0 < r → r ≤ r0 → 0 ≤ L →
        0 ≤ epsilon → epsilon ≤ epsilon0 → L ≤ 3*r^(-2*epsilon) →
          (9*(1+L)^2)^K ≤ r^(-e) ∧ ((modulus L)^(2*K):ℝ) ≤ r^(-e) := by
  let epsilon0 := e/(16*((K:ℝ)+1))
  have hepsilon0 : 0 < epsilon0 := by dsimp [epsilon0]; positivity
  have hC : (0:ℝ) < (144:ℝ)^K := by positivity
  obtain ⟨r0,hr0,hr01,Hcut⟩ := exists_small_power_cutoff
    (show 0 < e/2 by linarith only [he]) (show 0 < 1/(144:ℝ)^K by positivity)
  refine ⟨epsilon0,r0,hepsilon0,le_rfl,hr0,hr01,?_⟩
  intro r L epsilon hr hsmall hL heps hepsCap hLip
  have hr1 : r ≤ 1 := hsmall.trans hr01
  have hsmallPower : r^(e/2) ≤ 1/(144:ℝ)^K := Hcut r hr hsmall
  have hprod : (144:ℝ)^K*r^(e/2) ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp hsmallPower
    simpa only [mul_comm] using hh
  have hfixed : (144:ℝ)^K ≤ r^(-(e/2)) := by
    rw [Real.rpow_neg hr.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hr (e/2))).mpr hprod
  have hexponent : 4*(K:ℝ)*epsilon ≤ e/4 := by
    change epsilon ≤ e/(16*((K:ℝ)+1)) at hepsCap
    have hh := (le_div_iff₀ (show 0 < 16*((K:ℝ)+1) by positivity)).mp hepsCap
    nlinarith only [hh,heps]
  have hpaid : (9*(1+L)^2)^K ≤ r^(-e) := by
    calc
      (9*(1+L)^2)^K ≤ (144:ℝ)^K*r^(-(4*(K:ℝ)*epsilon)) :=
        palette_le_explicit_power K hr hr1 hL heps hLip
      _ ≤ r^(-(e/2))*r^(-(4*(K:ℝ)*epsilon)) :=
        mul_le_mul_of_nonneg_right hfixed (Real.rpow_nonneg hr.le _)
      _ = r^(-(e/2)-4*(K:ℝ)*epsilon) := by
        rw [←Real.rpow_add hr]
        congr 1
      _ ≤ r^(-e) := Real.rpow_le_rpow_of_exponent_ge hr hr1
        (by linarith only [hexponent,he])
  exact ⟨hpaid,(modulus_cost L hL K).trans hpaid⟩

end NativeMatrixHeightBudget
