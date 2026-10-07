import Theorems.Thm_StickyKakeya4_native_paid_third_budget
import Theorems.Thm_StickyKakeya4_native_height_metric_power
import Theorems.Thm_StickyKakeya4_native_general_rank_scalar_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativePaidXYParameters
open NativeFixedCompactKakeyaExponent NativeGeneralRankScalarBudget NativeRetainedSliceBudgetSource

/-- All finite cardinalities and rank margins can be fixed before the
relative engine, tau and the original source. The zero-gap branches are
retained by the general hierarchy supplier. -/
theorem exists_parameters (epsilonGraph epsilonPaid : ℝ)
    (hGraph : 0 < epsilonGraph) (hPaid : 0 < epsilonPaid) (hk : 0 < extremalExponent)
    (Kmin Jmin : ℕ) :
    ∃Khalf Jhorizontal : ℕ,Kmin ≤ Khalf ∧ 3 ≤ Khalf ∧
      1/((2*Khalf:ℕ):ℝ) ≤ epsilonGraph/2 ∧ Jmin ≤ Jhorizontal ∧ 0 < Jhorizontal ∧
      3/(Jhorizontal:ℝ) ≤ epsilonPaid/32 ∧
    ∃eta0 c : ℝ,0 < eta0 ∧ eta0 ≤ extremalExponent/2 ∧ eta0 ≤ epsilonGraph ∧
      eta0 ≤ 1 ∧ eta0 ≤ epsilonPaid/8192 ∧
      0 < c ∧ c ≤ 1/2 ∧ c ≤ 1/(eta0+1) ∧
      c ≤ positiveGap extremalExponent/(256*(eta0+1)) ∧ c ≤ epsilonGraph/24 ∧
      c ≤ quotientTolerance (epsilonPaid/4)/24 ∧ c ≤ quotientTolerance (epsilonPaid/16)/24 := by
  obtain ⟨Khalf,_hKhalf,hKmin,hgrain⟩ :=
    NativeHeightMetricPower.exists_grain_count epsilonGraph hGraph (max Kmin 3)
  obtain ⟨N,hN⟩ := exists_nat_gt (96/epsilonPaid)
  let Jhorizontal := max (N+1) Jmin
  have hJ : 0 < Jhorizontal := lt_of_lt_of_le (by omega : 0 < N+1) (le_max_left _ _)
  have hJreal : (0:ℝ) < Jhorizontal := by exact_mod_cast hJ
  have hNJ : (N:ℝ) < Jhorizontal := by exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_left (N+1) Jmin))
  have hlarge : 96 < (Jhorizontal:ℝ)*epsilonPaid := (div_lt_iff₀ hPaid).mp (hN.trans hNJ)
  have hJloss : 3/(Jhorizontal:ℝ) ≤ epsilonPaid/32 := (div_le_iff₀ hJreal).mpr (by nlinarith only [hlarge])
  let eta0 := min (extremalExponent/2) (min epsilonGraph (min 1 (epsilonPaid/8192)))
  have he0 : 0 < eta0 := lt_min (by positivity) (lt_min hGraph (lt_min (by norm_num) (by positivity)))
  have heK : eta0 ≤ extremalExponent/2 := min_le_left _ _
  have heGraph : eta0 ≤ epsilonGraph := (min_le_right _ _).trans (min_le_left _ _)
  have heRest : eta0 ≤ min 1 (epsilonPaid/8192) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c0,hc0,hc08,hcUnit,hcGap⟩ := exists_uniform_hierarchy extremalExponent eta0 hk he0.le
  have hqXY : 0 < quotientTolerance (epsilonPaid/4) := (quotientTolerance_bounds (show 0 < epsilonPaid/4 by positivity)).1
  have hqX : 0 < quotientTolerance (epsilonPaid/16) := (quotientTolerance_bounds (show 0 < epsilonPaid/16 by positivity)).1
  let c := min c0 (min (epsilonGraph/24)
    (min (quotientTolerance (epsilonPaid/4)/24) (quotientTolerance (epsilonPaid/16)/24)))
  have hc : 0 < c := lt_min hc0 (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hcc : c ≤ c0 := min_le_left _ _
  have hcRest : c ≤ min (epsilonGraph/24)
      (min (quotientTolerance (epsilonPaid/4)/24) (quotientTolerance (epsilonPaid/16)/24)) := min_le_right _ _
  refine ⟨Khalf,Jhorizontal,(le_max_left _ _).trans hKmin,(le_max_right _ _).trans hKmin,
    hgrain,le_max_right _ _,hJ,hJloss,eta0,c,he0,heK,heGraph,
    heRest.trans (min_le_left _ _),heRest.trans (min_le_right _ _),hc,
    hcc.trans (hc08.trans (by norm_num)),hcc.trans hcUnit,hcc.trans hcGap,
    hcRest.trans (min_le_left _ _),(hcRest.trans (min_le_right _ _)).trans (min_le_left _ _),
    (hcRest.trans (min_le_right _ _)).trans (min_le_right _ _)⟩

end NativePaidXYParameters
