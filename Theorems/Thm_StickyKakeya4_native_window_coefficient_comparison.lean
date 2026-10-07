import Theorems.Thm_StickyKakeya4_native_window_source_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeWindowCoefficientComparison
open NativeReferenceColumnExponents

/-- The new height endpoint and halo losses are one explicit fixed factor.
This does not spend any quotient or coordinate-change allowance. -/
lemma geometric_factor_bound :
    8*NativeVariableHeightNumeratorUpper.pairUpperConstant*
        NativeVariableHeightSourceBridge.comparisonCost^2 ≤
      65536*NativeAnisotropicPairNumerator.pairUpperConstant*
        NativeAnisotropicGlobalSourceBridge.comparisonCost^2 := by
  have hV := NativeOriginalPrunedMass.volumeConstant_pos
  norm_num [NativeVariableHeightNumeratorUpper.pairUpperConstant,
    NativeVariableHeightNumeratorUpper.shortRowColumnCost,NativeVariableHeightSourceBridge.comparisonCost,
    NativeVariableHeightRowLower.chargeConstant,NativeAnisotropicPairNumerator.pairUpperConstant,
    NativeAnisotropicPairNumerator.shortRowColumnCost,NativeAnisotropicGlobalSourceBridge.comparisonCost,
    NativeAnisotropicRowCountLower.chargeConstant]
  nlinarith only [hV]

/-- For identical physical source profiles, the variable-height U/L is at
most65536 times the fixed-height U/L. All source parameters remain literal;
the factor must be paid together with later quotient/coordinate constants. -/
theorem source_ratio_le {delta zeta population eps fullLower fullUpper : ℝ}
    (hd : 0 < delta) (hpopulation : 0 < population) (heps : 0 < eps)
    (hL : 0 < fullLower) (hU : 0 < fullUpper) :
    (8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*delta^(-2*zeta))/
        ((eps/NativeVariableHeightSourceBridge.comparisonCost)*fullLower))/
        lowerCountCoefficient delta zeta population
          ((NativeVariableHeightSourceBridge.comparisonCost/eps)*fullUpper) ≤
      65536*(upperCountCoefficient delta zeta
          ((eps/NativeAnisotropicGlobalSourceBridge.comparisonCost)*fullLower)/
        lowerCountCoefficient delta zeta population
          ((NativeAnisotropicGlobalSourceBridge.comparisonCost/eps)*fullUpper)) := by
  let T := (delta^(-2*zeta)*43904*fullUpper)/(eps^2*fullLower*(population*delta^(2*zeta)))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ho := NativeAnisotropicGlobalSourceBridge.comparisonCost_pos
  have hn := NativeVariableHeightSourceBridge.comparisonCost_pos
  have hp : delta^(2*zeta)≠0 := (Real.rpow_pos_of_pos hd _).ne'
  have hnew :
      (8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*delta^(-2*zeta))/
        ((eps/NativeVariableHeightSourceBridge.comparisonCost)*fullLower))/
        lowerCountCoefficient delta zeta population
          ((NativeVariableHeightSourceBridge.comparisonCost/eps)*fullUpper)=
      (8*NativeVariableHeightNumeratorUpper.pairUpperConstant*
        NativeVariableHeightSourceBridge.comparisonCost^2)*T := by
    dsimp [lowerCountCoefficient,T]
    field_simp [hn.ne',heps.ne',hL.ne',hU.ne',hpopulation.ne',hp]
  have hold : upperCountCoefficient delta zeta
          ((eps/NativeAnisotropicGlobalSourceBridge.comparisonCost)*fullLower)/
        lowerCountCoefficient delta zeta population
          ((NativeAnisotropicGlobalSourceBridge.comparisonCost/eps)*fullUpper)=
      (NativeAnisotropicPairNumerator.pairUpperConstant*
        NativeAnisotropicGlobalSourceBridge.comparisonCost^2)*T := by
    dsimp [lowerCountCoefficient,upperCountCoefficient,T]
    field_simp [ho.ne',heps.ne',hL.ne',hU.ne',hpopulation.ne',hp]
  rw [hnew,hold]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right geometric_factor_bound hT

end NativeWindowCoefficientComparison
