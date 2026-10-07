import Theorems.Thm_StickyKakeya4_native_general_rank_scalar_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeHierarchyCap
open NativeGeneralRankScalarBudget

/-- Lowering the eventual rank-loss parameter preserves both hierarchy
inequalities for an already fixed c. -/
theorem bounds_mono {kappa etaCap eta0 c : ℝ} (hk : 0 < kappa)
    (he0 : 0 ≤ eta0) (he : eta0 ≤ etaCap)
    (hUnit : c ≤ 1/(etaCap+1))
    (hGap : c ≤ positiveGap kappa/(256*(etaCap+1))) :
    c ≤ 1/(eta0+1) ∧ c ≤ positiveGap kappa/(256*(eta0+1)) := by
  constructor
  · exact hUnit.trans (div_le_div_of_nonneg_left (by norm_num)
      (by linarith only [he0]) (by linarith only [he]))
  · exact hGap.trans (div_le_div_of_nonneg_left (positiveGap_pos hk).le
      (by positivity) (by linarith only [he]))

/-- Choose c from a fixed eta cap and all independent c constraints before
querying a later admissibility exponent. The actual eta0 may then be chosen
arbitrarily smaller, with this same c and its original bounds. -/
theorem exists_uniform_cap (kappa etaCap cMax : ℝ)
    (hk : 0 < kappa) (hCap : 0 ≤ etaCap) (hcMax : 0 < cMax) :
    ∃c : ℝ,0 < c ∧ c ≤ 1/8 ∧ c ≤ cMax ∧
      ∀eta0 : ℝ,0 ≤ eta0 → eta0 ≤ etaCap →
        c ≤ 1/(eta0+1) ∧ c ≤ positiveGap kappa/(256*(eta0+1)) := by
  obtain ⟨c0,hc0,hc08,hUnit,hGap⟩ := exists_uniform_hierarchy kappa etaCap hk hCap
  refine ⟨min c0 cMax,lt_min hc0 hcMax,(min_le_left _ _).trans hc08,min_le_right _ _,?_⟩
  intro eta0 he0 he
  exact bounds_mono hk he0 he ((min_le_left _ _).trans hUnit) ((min_le_left _ _).trans hGap)

end NativeHierarchyCap
