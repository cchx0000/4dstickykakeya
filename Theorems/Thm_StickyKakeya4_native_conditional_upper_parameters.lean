import Theorems.Thm_StickyKakeya4_native_conditional_grid_power_cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000

noncomputable section
namespace NativeConditionalUpperParameters

/-- All relative-engine and fixed-menu parameters are chosen after the
positive minimum stopping exponent but before tau and the source datum.
Every possible selected rank shares this one choice. -/
theorem exists_upper_parameters (amin loss : ℝ) (ha : 0< amin) (hl : 0< loss) (hl1 : loss≤ 1) :
    ∃(epsilon window budget seedBound : ℝ) (K : ℕ),
      0< epsilon ∧ 0< window ∧ 0< budget ∧ 0< seedBound ∧ 0< K ∧
      3*window≤ budget ∧ window≤ amin ∧
      ∀power seed : ℝ,amin≤ power → seed≤ seedBound →
        (budget+seed/4)/power+epsilon/2+2/(K:ℝ)≤ loss := by
  let epsilon := loss/4
  let window := amin*loss/32
  let budget := amin*loss/8
  let seedBound := amin*loss/2
  obtain ⟨K,hK⟩ := exists_nat_gt (16/loss)
  have hKR : (0:ℝ)<K := (div_pos (by norm_num) hl).trans hK
  have hKN : 0< K := by exact_mod_cast hKR
  have hgrid : 2/(K:ℝ)≤ loss/8 := by
    have hh : 16< (K:ℝ)*loss := (div_lt_iff₀ hl).mp hK
    apply (div_le_iff₀ hKR).mpr
    nlinarith only [hh]
  refine ⟨epsilon,window,budget,seedBound,K,by dsimp [epsilon]; positivity,
    by dsimp [window]; positivity,by dsimp [budget]; positivity,
    by dsimp [seedBound]; positivity,hKN,?_,?_,?_⟩
  · dsimp [window,budget]
    nlinarith only [mul_pos ha hl]
  · dsimp [window]
    have hh := mul_le_mul_of_nonneg_left hl1 ha.le
    nlinarith only [hh,ha]
  · intro power seed hpower hseed
    have hpower0 : 0< power := ha.trans_le hpower
    have hnum : budget+seed/4≤ power*(loss/4) := by
      have hh := mul_le_mul_of_nonneg_right hpower hl.le
      dsimp [budget,seedBound] at *
      nlinarith only [hh,hseed]
    have hdiv : (budget+seed/4)/power≤ loss/4 := (div_le_iff₀ hpower0).mpr (by nlinarith only [hnum])
    dsimp [epsilon]
    linarith only [hdiv,hgrid,hl]

end NativeConditionalUpperParameters
